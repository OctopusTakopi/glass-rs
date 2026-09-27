//! Coverage-guided differential fuzzing: every public `Glass` operation
//! against a `BTreeMap` oracle with exact (u128, then saturated) costs.
//!
//! Keys come in the shapes that stress different internals: dense (shared
//! leaves and ancestors), scattered (isolated leaves, whose removal prunes
//! ancestors), 2^18-strided (one hash bucket, chains past the 5-probe
//! bound), edges (0, leaf boundaries, u32::MAX), and neighbours of existing
//! keys, of the best keys in particular. Order sizes can be pinned to level
//! boundaries (exactly the first n levels, ± a little), where consumption
//! code has its edge cases. `Bulk` crosses the 4096-level trie capacity in
//! one step. After every operation `check_invariants` verifies the whole
//! structure, so a corruption is caught when it happens.
//!
//! State-relative keys and sizes matter: with raw numbers only, 16 jobs ran
//! 1.7M inputs without once producing the 4-operation sequence behind the
//! stale-path-cache bug (insert x, insert x-1, buy exactly x-1, pop x); with
//! them it is found in seconds.
//!
//! cargo fuzz run ops    (fuzz_targets/ops.rs drives `run`)

use arbitrary::Arbitrary;
use glass_rs::Glass;
use std::collections::BTreeMap;

#[derive(Arbitrary, Debug, Clone, Copy)]
pub enum Key {
    Dense(u16),
    Sparse(u32),
    Collide(u8, u8),
    Edge(u8),
    /// The `idx`-th existing key (mod len), moved by `delta`.
    Near(u16, i8),
    /// The lowest / highest key, moved by `delta`.
    Min(i8),
    Max(i8),
}

#[derive(Arbitrary, Debug, Clone, Copy)]
pub enum Qty {
    Zero,
    Small(u16),
    Raw(u64),
    /// Just below / above the leaf-sum exactness bound (2^52).
    NearBound(bool, u8),
    NearMax(u16),
}

#[derive(Arbitrary, Debug, Clone, Copy)]
pub enum Size {
    Small(u16),
    Thousands(u32),
    Raw(u64),
    All,
    /// Exactly the quantity of the first `n + 1` levels on the side being
    /// consumed, plus `delta`.
    Levels(u8, i8),
}

#[derive(Arbitrary, Debug, Clone, Copy)]
pub enum Op {
    Insert(Key, Qty),
    Remove(Key),
    Get(Key),
    Update(Key, i64),
    Buy(Size),
    Sell(Size),
    BuyCost(Size),
    SellCost(Size),
    RemoveByIndex(u16),
    PopFirst,
    PopLast,
    Next(Key),
    Prev(Key),
    Range(Key, Key),
    Top(u16),
    /// `split_off`, compare both halves, then `extend` the upper half back.
    SplitOff(Key),
    Retain(u8),
    Bulk {
        start: Key,
        stride: u8,
        count: u16,
        qty: Qty,
    },
    Clear,
    Check,
}

const EDGES: [u32; 12] = [
    0,
    1,
    62,
    63,
    64,
    65,
    4095,
    4096,
    1 << 31,
    u32::MAX - 64,
    u32::MAX - 1,
    u32::MAX,
];

fn key(k: Key, m: &BTreeMap<u32, u64>) -> u32 {
    match k {
        Key::Dense(n) => 1000 + (n % 8192) as u32,
        Key::Sparse(n) => n,
        Key::Collide(c, o) => ((c as u32 % 32) << 18) | (o as u32 % 4),
        Key::Edge(i) => EDGES[i as usize % EDGES.len()],
        Key::Near(i, d) => match m.len() {
            0 => d as u8 as u32,
            n => m
                .keys()
                .nth(i as usize % n)
                .copied()
                .unwrap_or(0)
                .wrapping_add_signed(d as i32),
        },
        Key::Min(d) => m
            .keys()
            .next()
            .copied()
            .unwrap_or(1 << 31)
            .wrapping_add_signed(d as i32),
        Key::Max(d) => m
            .keys()
            .next_back()
            .copied()
            .unwrap_or(1 << 31)
            .wrapping_add_signed(d as i32),
    }
}

fn qty(q: Qty) -> u64 {
    match q {
        Qty::Zero => 0,
        Qty::Small(n) => n as u64,
        Qty::Raw(n) => n,
        Qty::NearBound(above, d) => {
            if above {
                (1 << 52) + d as u64
            } else {
                (1 << 52) - 1 - d as u64
            }
        }
        Qty::NearMax(d) => u64::MAX - d as u64,
    }
}

fn size(s: Size, m: &BTreeMap<u32, u64>, from_top: bool) -> u64 {
    match s {
        Size::Small(n) => n as u64,
        Size::Thousands(n) => n as u64 * 1_000,
        Size::Raw(n) => n,
        Size::All => u64::MAX,
        Size::Levels(n, d) => {
            let levels: Box<dyn Iterator<Item = &u64>> = if from_top {
                Box::new(m.values().rev())
            } else {
                Box::new(m.values())
            };
            // Mostly the first few levels, where executions end most often.
            let n = if n < 192 { n % 4 } else { n };
            let sum = levels
                .take(n as usize + 1)
                .fold(0u64, |a, &q| a.saturating_add(q));
            sum.saturating_add_signed(d as i64)
        }
    }
}

/// Market order against the oracle: `Σ key·qty`, exact then saturated.
fn execute(m: &mut BTreeMap<u32, u64>, mut size: u64, from_top: bool, consume: bool) -> u64 {
    let mut cost = 0u128;
    let mut taken = Vec::new();
    let mut levels: Box<dyn Iterator<Item = (&u32, &u64)>> = if from_top {
        Box::new(m.iter().rev())
    } else {
        Box::new(m.iter())
    };
    while size > 0 {
        let Some((&k, &q)) = levels.next() else { break };
        let t = q.min(size);
        cost += k as u128 * t as u128;
        size -= t;
        taken.push((k, t));
    }
    drop(levels);
    if consume {
        for (k, t) in taken {
            let q = m.get_mut(&k).unwrap();
            *q -= t;
            if *q == 0 {
                m.remove(&k);
            }
        }
    }
    cost.min(u64::MAX as u128) as u64
}

fn check(g: &Glass, m: &BTreeMap<u32, u64>, what: &str) {
    // The structural self-check catches corruption when it happens, not
    // only once a later operation happens to expose it.
    if let Err(e) = g.check_invariants() {
        panic!("invariant broken after {what}: {e}");
    }
    assert_eq!(g.len(), m.len(), "len after {what}");
    assert_eq!(g.is_empty(), m.is_empty(), "is_empty after {what}");
    let kv = |e: Option<(&u32, &u64)>| e.map(|(&k, &v)| (k, v));
    assert_eq!(g.min(), kv(m.first_key_value()), "min after {what}");
    assert_eq!(g.max(), kv(m.last_key_value()), "max after {what}");
    assert_eq!(g.first_key_value(), g.min(), "first_key_value after {what}");
    assert_eq!(g.last_key_value(), g.max(), "last_key_value after {what}");
    assert!(g.glass_size() <= 4096, "trie over capacity after {what}");
}

fn check_full(g: &Glass, m: &BTreeMap<u32, u64>, what: &str) {
    check(g, m, what);
    assert!(
        g.iter().eq(m.iter().map(|(&k, &v)| (k, v))),
        "iter after {what}"
    );
    assert!(g.keys().eq(m.keys().copied()), "keys after {what}");
    assert!(g.values().eq(m.values().copied()), "values after {what}");
    for (&k, &v) in m.iter().step_by(1 + m.len() / 64) {
        assert_eq!(g.get(k), Some(v), "get({k}) after {what}");
        assert!(g.contains_key(k), "contains_key({k}) after {what}");
    }
}

/// Runs `ops` against glass-rs and the oracle, panicking on any difference
/// or broken invariant. The whole book is compared every 32 operations and
/// after bulk changes; `check_invariants` runs after every operation.
pub fn run(ops: &[Op]) {
    let mut g = Glass::new();
    let mut m: BTreeMap<u32, u64> = BTreeMap::new();
    let mut buf = Vec::new();
    for (i, &op) in ops.iter().enumerate() {
        let what = format!("op #{i} {op:?}");
        match op {
            Op::Insert(k, q) => {
                let (k, q) = (key(k, &m), qty(q));
                g.insert(k, q);
                if q == 0 {
                    m.remove(&k);
                } else {
                    m.insert(k, q);
                }
            }
            Op::Remove(k) => {
                let k = key(k, &m);
                assert_eq!(g.remove(k), m.remove(&k), "{what}");
            }
            Op::Get(k) => {
                let k = key(k, &m);
                assert_eq!(g.get(k), m.get(&k).copied(), "{what}");
                assert_eq!(
                    g.get_key_value(k),
                    m.get_key_value(&k).map(|(&a, &b)| (a, b)),
                    "{what}"
                );
            }
            Op::Update(k, d) => {
                let k = key(k, &m);
                let f = |q: &mut u64| *q = q.saturating_add_signed(d);
                let want = match m.get_mut(&k) {
                    Some(q) => {
                        f(q);
                        if *q == 0 {
                            m.remove(&k);
                        }
                        true
                    }
                    None => false,
                };
                assert_eq!(g.update_value(k, f), want, "{what}");
            }
            Op::Buy(s) => {
                let s = size(s, &m, false);
                assert_eq!(
                    g.buy_shares(s),
                    execute(&mut m, s, false, true),
                    "{what} = {s}"
                );
            }
            Op::Sell(s) => {
                let s = size(s, &m, true);
                assert_eq!(
                    g.sell_shares(s),
                    execute(&mut m, s, true, true),
                    "{what} = {s}"
                );
            }
            Op::BuyCost(s) => {
                let s = size(s, &m, false);
                assert_eq!(
                    g.compute_buy_cost(s),
                    execute(&mut m, s, false, false),
                    "{what} = {s}"
                );
            }
            Op::SellCost(s) => {
                let s = size(s, &m, true);
                assert_eq!(
                    g.compute_sell_cost(s),
                    execute(&mut m, s, true, false),
                    "{what} = {s}"
                );
            }
            Op::RemoveByIndex(i) => {
                let i = i as usize % (m.len() + 2);
                let want = m.keys().nth(i).copied().map(|k| (k, m.remove(&k).unwrap()));
                assert_eq!(g.remove_by_index(i), want, "{what}");
            }
            Op::PopFirst => assert_eq!(g.pop_first(), m.pop_first(), "{what}"),
            Op::PopLast => assert_eq!(g.pop_last(), m.pop_last(), "{what}"),
            Op::Next(k) => {
                let k = key(k, &m);
                let want = m
                    .range((std::ops::Bound::Excluded(k), std::ops::Bound::Unbounded))
                    .next();
                assert_eq!(g.next_level(k), want.map(|(&a, &b)| (a, b)), "{what}");
            }
            Op::Prev(k) => {
                let k = key(k, &m);
                let want = m.range(..k).next_back();
                assert_eq!(g.prev_level(k), want.map(|(&a, &b)| (a, b)), "{what}");
            }
            Op::Range(a, b) => {
                let (a, b) = (key(a, &m), key(b, &m));
                let (lo, hi) = (a.min(b), a.max(b));
                assert!(
                    g.range(lo..=hi).eq(m.range(lo..=hi).map(|(&k, &v)| (k, v))),
                    "{what}: range({lo}..={hi})"
                );
                assert!(
                    g.range(lo..hi).eq(m.range(lo..hi).map(|(&k, &v)| (k, v))),
                    "{what}: range({lo}..{hi})"
                );
                assert!(
                    g.range(..lo).eq(m.range(..lo).map(|(&k, &v)| (k, v))),
                    "{what}: range(..{lo})"
                );
            }
            Op::Top(n) => {
                let n = n as usize % 300;
                let got = g.top_levels(n, &mut buf);
                let want: Vec<(u32, u64)> = m.iter().take(n).map(|(&k, &v)| (k, v)).collect();
                assert_eq!(got, want.len(), "{what}");
                assert_eq!(buf, want, "{what}");
            }
            Op::SplitOff(k) => {
                let k = key(k, &m);
                let upper = g.split_off(k);
                let m_upper = m.split_off(&k);
                check_full(&g, &m, &what);
                check_full(&upper, &m_upper, &format!("{what} (upper half)"));
                g.extend(upper.iter());
                m.extend(m_upper);
            }
            Op::Retain(r) => {
                let r = r as u32 % 7 + 2;
                g.retain(|k, v| !(k ^ v as u32).is_multiple_of(r));
                m.retain(|&k, &mut v| !(k ^ v as u32).is_multiple_of(r));
            }
            Op::Bulk {
                start,
                stride,
                count,
                qty: q,
            } => {
                let (mut k, step, q) = (key(start, &m), stride as u32 + 1, qty(q));
                for _ in 0..count % 6000 {
                    g.insert(k, q);
                    if q == 0 {
                        m.remove(&k);
                    } else {
                        m.insert(k, q);
                    }
                    k = k.wrapping_add(step);
                }
            }
            Op::Clear => {
                g.clear();
                m.clear();
            }
            Op::Check => check_full(&g, &m, &what),
        }
        check(&g, &m, &what);
        if i % 32 == 31 || matches!(op, Op::Bulk { .. } | Op::Retain(_) | Op::Clear) {
            check_full(&g, &m, &what);
        }
    }
    check_full(&g, &m, "the last op");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The stale-path-cache bug's trigger (fixed in glass-rs). With the bug
    /// present, the harness fails it at the `PopLast`, through
    /// `check_invariants` ("cached path ... leads out of the trie").
    #[test]
    fn stale_path_cache_pattern() {
        run(&[
            Op::Insert(Key::Sparse(0x9000_0005), Qty::Small(3)),
            Op::Insert(Key::Min(-1), Qty::Small(2)),
            Op::Buy(Size::Levels(0, 0)),
            Op::PopLast,
            Op::Insert(Key::Sparse(0x9100_0000), Qty::Small(1)),
            Op::Buy(Size::All),
        ]);
    }
}
