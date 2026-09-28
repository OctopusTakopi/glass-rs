//! Two implementations of the same order book, fed identical updates:
//! a conventional `BTreeMap` book and a `glass_rs::Glass` book.
//!
//! Glass keeps its lowest 4096 keys in the fast trie, so its asks are keyed by
//! tick price and its bids by the bit-inverted tick price (`!ticks`): each
//! side's best level is its lowest key, so each side's top of book lives in
//! its trie.

use glass_rs::Glass;
use std::collections::BTreeMap;

/// One price level: absolute size `lots` at `ticks`; 0 removes the level.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Level {
    pub ticks: u32,
    pub lots: u64,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Side {
    Bid,
    Ask,
}

pub trait OrderBook {
    fn clear(&mut self);
    /// Sets the absolute size at a price; 0 removes the level.
    fn set(&mut self, side: Side, l: Level);
    fn best(&self, side: Side) -> Option<Level>;
    /// Best `n` levels of one side, best first, into `out`.
    fn top(&mut self, side: Side, n: usize, out: &mut Vec<Level>);
    /// `(bid levels, ask levels)`.
    fn levels(&self) -> (usize, usize);
    /// Market order of `lots` from the best price: `Σ ticks·lots` (saturating)
    /// and the lots filled.
    fn market(&self, side: Side, lots: u64) -> (u64, u64);
}

// ---------------------------------------------------------------- BTreeMap

#[derive(Default)]
pub struct BTreeBook {
    bids: BTreeMap<u32, u64>,
    asks: BTreeMap<u32, u64>,
}

impl OrderBook for BTreeBook {
    fn clear(&mut self) {
        self.bids.clear();
        self.asks.clear();
    }

    #[inline]
    fn set(&mut self, side: Side, l: Level) {
        let m = if side == Side::Ask {
            &mut self.asks
        } else {
            &mut self.bids
        };
        if l.lots == 0 {
            m.remove(&l.ticks);
        } else {
            m.insert(l.ticks, l.lots);
        }
    }

    fn best(&self, side: Side) -> Option<Level> {
        let kv = if side == Side::Ask {
            self.asks.first_key_value()
        } else {
            self.bids.last_key_value()
        };
        kv.map(|(&ticks, &lots)| Level { ticks, lots })
    }

    fn top(&mut self, side: Side, n: usize, out: &mut Vec<Level>) {
        out.clear();
        let lv = |(&ticks, &lots): (&u32, &u64)| Level { ticks, lots };
        if side == Side::Ask {
            out.extend(self.asks.iter().take(n).map(lv));
        } else {
            out.extend(self.bids.iter().rev().take(n).map(lv));
        }
    }

    fn levels(&self) -> (usize, usize) {
        (self.bids.len(), self.asks.len())
    }

    fn market(&self, side: Side, lots: u64) -> (u64, u64) {
        fn walk<'a>(it: impl Iterator<Item = (&'a u32, &'a u64)>, mut left: u64) -> (u64, u64) {
            let want = left;
            let mut cost = 0u64;
            for (&p, &q) in it {
                if left == 0 {
                    break;
                }
                let t = q.min(left);
                cost = cost.saturating_add((p as u64).saturating_mul(t));
                left -= t;
            }
            (cost, want - left)
        }
        if side == Side::Ask {
            walk(self.asks.iter(), lots)
        } else {
            walk(self.bids.iter().rev(), lots)
        }
    }
}

// ---------------------------------------------------------------- glass-rs

pub struct GlassBook {
    asks: Glass,
    bids: Glass, // keyed by !ticks
    // Total resting size per side, so a market-order estimate knows how much
    // actually fills (needed to undo the bid key inversion, see `market`).
    bid_lots: u64,
    ask_lots: u64,
    buf: Vec<(u32, u64)>,
}

impl Default for GlassBook {
    fn default() -> Self {
        GlassBook {
            asks: Glass::new(),
            bids: Glass::new(),
            bid_lots: 0,
            ask_lots: 0,
            buf: Vec::with_capacity(64),
        }
    }
}

impl OrderBook for GlassBook {
    fn clear(&mut self) {
        self.asks.clear();
        self.bids.clear();
        self.bid_lots = 0;
        self.ask_lots = 0;
    }

    #[inline]
    fn set(&mut self, side: Side, l: Level) {
        let (g, total, key) = match side {
            Side::Ask => (&mut self.asks, &mut self.ask_lots, l.ticks),
            Side::Bid => (&mut self.bids, &mut self.bid_lots, !l.ticks),
        };
        let old = g.get(key).unwrap_or(0);
        *total = *total - old + l.lots;
        g.insert(key, l.lots); // 0 deletes
    }

    fn best(&self, side: Side) -> Option<Level> {
        match side {
            Side::Ask => self.asks.min().map(|(k, q)| Level { ticks: k, lots: q }),
            Side::Bid => self.bids.min().map(|(k, q)| Level { ticks: !k, lots: q }),
        }
    }

    fn top(&mut self, side: Side, n: usize, out: &mut Vec<Level>) {
        let g = if side == Side::Ask {
            &self.asks
        } else {
            &self.bids
        };
        g.top_levels(n, &mut self.buf);
        out.clear();
        out.extend(self.buf.iter().map(|&(k, q)| Level {
            ticks: if side == Side::Ask { k } else { !k },
            lots: q,
        }));
    }

    fn levels(&self) -> (usize, usize) {
        (self.bids.len(), self.asks.len())
    }

    fn market(&self, side: Side, lots: u64) -> (u64, u64) {
        match side {
            Side::Ask => (self.asks.compute_buy_cost(lots), lots.min(self.ask_lots)),
            Side::Bid => {
                // Bids are keyed by !ticks = u32::MAX - ticks, so glass's
                // cheapest-first estimate over them is u32::MAX·filled − Σ ticks·lots.
                // That is exact while u32::MAX·filled fits in u64 (then glass's
                // sum, which is at most that, cannot saturate either). A
                // low-priced coin with huge sizes fills far more (1000SATS: ~1e11
                // lots), where the inversion cannot be undone: walk the levels.
                let filled = lots.min(self.bid_lots);
                let base = u32::MAX as u128 * filled as u128;
                if base <= u64::MAX as u128 {
                    let inverted = self.bids.compute_buy_cost(lots) as u128;
                    ((base - inverted) as u64, filled)
                } else {
                    let mut cost = 0u128;
                    let mut left = filled;
                    for (k, q) in self.bids.iter() {
                        if left == 0 {
                            break;
                        }
                        let take = q.min(left);
                        cost += (!k) as u128 * take as u128;
                        left -= take;
                    }
                    (cost.min(u64::MAX as u128) as u64, filled)
                }
            }
        }
    }
}

impl GlassBook {
    /// Every level of one side, best first (for the full cross-check).
    pub fn all(&self, side: Side) -> Vec<Level> {
        match side {
            Side::Ask => self
                .asks
                .iter()
                .map(|(k, q)| Level { ticks: k, lots: q })
                .collect(),
            Side::Bid => self
                .bids
                .iter()
                .map(|(k, q)| Level { ticks: !k, lots: q })
                .collect(),
        }
    }
}

impl BTreeBook {
    /// Levels of `side` from the best price back to `limit` inclusive (bids
    /// at or above it, asks at or below it), counting no further than `cap`.
    pub fn count_from(&self, side: Side, limit: u32, cap: usize) -> usize {
        match side {
            Side::Bid => self.bids.range(limit..).take(cap).count(),
            Side::Ask => self.asks.range(..=limit).take(cap).count(),
        }
    }

    pub fn all(&self, side: Side) -> Vec<Level> {
        let lv = |(&ticks, &lots): (&u32, &u64)| Level { ticks, lots };
        match side {
            Side::Ask => self.asks.iter().map(lv).collect(),
            Side::Bid => self.bids.iter().rev().map(lv).collect(),
        }
    }
}

/// Order sizes (in lots) of the full check's estimates: a single level for
/// BTC up to many levels of a coin that trades in billions of lots. Against
/// bid keys (!ticks ~ 4.29e9), 4e9 lots cost ~1.72e19: exact, just under
/// u64::MAX (1.84e19); 1e10 lots and up saturate.
const MARKET_SIZES: [u64; 10] = [
    1,
    100,
    10_000,
    1_000_000,
    100_000_000,
    1_000_000_000,
    4_000_000_000,
    10_000_000_000,
    1_000_000_000_000,
    u64::MAX,
];

/// Cross-checks the two books. `full` compares every level, market
/// estimates of several sizes, and glass's own cost estimates in its key
/// space (O(book)); otherwise only O(1) facts.
pub fn cross_check(g: &GlassBook, b: &BTreeBook, full: bool) -> Result<(), String> {
    if g.levels() != b.levels() {
        return Err(format!(
            "level counts glass {:?} != btree {:?}",
            g.levels(),
            b.levels()
        ));
    }
    for (side, name) in [(Side::Bid, "bid"), (Side::Ask, "ask")] {
        if g.best(side) != b.best(side) {
            return Err(format!(
                "best {name}: glass {:?} != btree {:?}",
                g.best(side),
                b.best(side)
            ));
        }
        if full {
            let (ga, ba) = (g.all(side), b.all(side));
            if let Some(i) = ga.iter().zip(&ba).position(|(x, y)| x != y) {
                return Err(format!(
                    "{name} level #{i}: glass {:?} != btree {:?}",
                    ga[i], ba[i]
                ));
            }
            for lots in MARKET_SIZES {
                if g.market(side, lots) != b.market(side, lots) {
                    return Err(format!(
                        "{name} market({lots}): glass {:?} != btree {:?}",
                        g.market(side, lots),
                        b.market(side, lots)
                    ));
                }
            }
            // `market` may avoid glass's estimators (see its bid arm), so
            // check them directly, in glass's key space, against an exact
            // u128 oracle. Bid keys are !ticks ~ 4.3e9, so on a coin with
            // huge sizes these sums pass u64 and exercise the saturation.
            let (glass, keys): (&Glass, Vec<(u32, u64)>) = match side {
                Side::Ask => (&g.asks, b.asks.iter().map(|(&t, &q)| (t, q)).collect()),
                Side::Bid => (
                    &g.bids,
                    b.bids.iter().rev().map(|(&t, &q)| (!t, q)).collect(),
                ),
            };
            for lots in MARKET_SIZES {
                let buy = (glass.compute_buy_cost(lots), greedy(keys.iter(), lots));
                let sell = (
                    glass.compute_sell_cost(lots),
                    greedy(keys.iter().rev(), lots),
                );
                if buy.0 != buy.1 || sell.0 != sell.1 {
                    return Err(format!(
                        "{name} key-space compute_buy_cost/compute_sell_cost({lots}): glass {:?} != oracle {:?}",
                        (buy.0, sell.0),
                        (buy.1, sell.1)
                    ));
                }
            }
        }
    }
    Ok(())
}

// ------------------------------------------------------- execution check

/// Replays a random mix of operations on copies of each side of the live
/// book, glass-rs against a `BTreeMap` oracle, comparing every result, the
/// length after every step, and the contents at the end. The live books only
/// ever see `insert`/`remove` and lookups; this puts real market-shaped data
/// through the consuming operations too (`buy_shares`, `sell_shares`,
/// `remove_by_index`, `pop_first`/`pop_last`, `update_value`) and the
/// navigation ones (`next_level`/`prev_level`, `range`,
/// `compute_sell_cost`). Returns the number of operations run.
pub fn exec_check(g: &GlassBook, b: &BTreeBook, rng: &mut u64) -> Result<u64, String> {
    const OPS: u64 = 200;
    for (name, glass, oracle) in [
        ("asks", &g.asks, b.asks.clone()),
        // Glass keys bids by !ticks; mirror that in the oracle.
        (
            "bids",
            &g.bids,
            b.bids.iter().map(|(&t, &q)| (!t, q)).collect(),
        ),
    ] {
        exec_side(glass, oracle, rng, OPS).map_err(|e| format!("{name}: {e}"))?;
    }
    Ok(2 * OPS)
}

fn exec_side(
    live: &Glass,
    mut m: BTreeMap<u32, u64>,
    rng: &mut u64,
    ops: u64,
) -> Result<(), String> {
    let mut next = || {
        *rng ^= *rng << 13;
        *rng ^= *rng >> 7;
        *rng ^= *rng << 17;
        *rng
    };
    let mut g: Glass = live.iter().collect();
    same(&g, &m).map_err(|e| format!("copy of the live book: {e}"))?;
    for i in 0..ops {
        let r = next();
        let total = m.values().fold(0u64, |a, &q| a.saturating_add(q));
        // A typical level's size: BTC's are ~1e3 lots, 1000SATS's ~1e8, so
        // sizes and quantities scale with it.
        let unit = (total / m.len().max(1) as u64).max(1);
        // Order sizes: mostly top-of-book, some deep, rarely a full sweep.
        let size = match r % 64 {
            0 => u64::MAX,
            1..=40 => 1 + (r >> 8) % unit.saturating_mul(3),
            _ => 1 + (r >> 8) % (total / 8 + 1),
        };
        // A key near the book: an existing one, a neighbour, or fresh.
        let key = {
            let r2 = next();
            match (m.len(), r2 % 4) {
                (0, _) | (_, 3) => (r2 >> 32) as u32,
                (n, d) => {
                    let k = *m.keys().nth((r2 >> 8) as usize % n).unwrap_or(&0);
                    k.wrapping_add(d as u32).wrapping_sub(1)
                }
            }
        };
        let op = (r >> 40) % 11;
        let check = |what: &str, got: String, want: String| -> Result<(), String> {
            if got == want {
                Ok(())
            } else {
                Err(format!("op #{i} {what}: glass {got} != oracle {want}"))
            }
        };
        match op {
            0 => check(
                &format!("buy_shares({size})"),
                g.buy_shares(size).to_string(),
                execute(&mut m, size, false).to_string(),
            )?,
            1 => check(
                &format!("sell_shares({size})"),
                g.sell_shares(size).to_string(),
                execute(&mut m, size, true).to_string(),
            )?,
            2 => {
                let mut peek = m.clone();
                check(
                    &format!("compute_buy_cost({size})"),
                    g.compute_buy_cost(size).to_string(),
                    execute(&mut peek, size, false).to_string(),
                )?;
                let mut peek = m.clone();
                check(
                    &format!("compute_sell_cost({size})"),
                    g.compute_sell_cost(size).to_string(),
                    execute(&mut peek, size, true).to_string(),
                )?;
            }
            3 => {
                let k = (next() as usize) % (m.len() + 1);
                let want = m
                    .keys()
                    .nth(k)
                    .copied()
                    .map(|key| (key, m.remove(&key).unwrap_or(0)));
                check(
                    &format!("remove_by_index({k})"),
                    format!("{:?}", g.remove_by_index(k)),
                    format!("{want:?}"),
                )?;
            }
            4 => check(
                "pop_first",
                format!("{:?}", g.pop_first()),
                format!("{:?}", m.pop_first()),
            )?,
            5 => check(
                "pop_last",
                format!("{:?}", g.pop_last()),
                format!("{:?}", m.pop_last()),
            )?,
            6 => {
                // Adjust by a signed delta; hitting 0 removes the level.
                let span = unit.min(i64::MAX as u64 / 2);
                let delta = (next() % (2 * span + 1)) as i64 - span as i64;
                let apply = |q: &mut u64| *q = q.saturating_add_signed(delta);
                let want = match m.get_mut(&key) {
                    Some(q) => {
                        apply(q);
                        if *q == 0 {
                            m.remove(&key);
                        }
                        true
                    }
                    None => false,
                };
                check(
                    &format!("update_value({key}, {delta:+})"),
                    g.update_value(key, apply).to_string(),
                    want.to_string(),
                )?;
            }
            7 => {
                let succ = m
                    .range(key.saturating_add(1)..)
                    .next()
                    .filter(|_| key < u32::MAX);
                let pred = m.range(..key).next_back();
                check(
                    &format!("next_level/prev_level({key})"),
                    format!("{:?} {:?}", g.next_level(key), g.prev_level(key)),
                    format!(
                        "{:?} {:?}",
                        succ.map(|(&k, &q)| (k, q)),
                        pred.map(|(&k, &q)| (k, q))
                    ),
                )?;
            }
            8 => {
                let hi = key.saturating_add((next() % 5_000) as u32);
                let sum = |it: &mut dyn Iterator<Item = (u32, u64)>| {
                    it.fold((0usize, 0u128), |(n, s), (k, q)| {
                        (n + 1, s + k as u128 * q as u128)
                    })
                };
                check(
                    &format!("range({key}..={hi})"),
                    format!("{:?}", sum(&mut g.range(key..=hi))),
                    format!("{:?}", sum(&mut m.range(key..=hi).map(|(&k, &q)| (k, q)))),
                )?;
            }
            9 => {
                // Refill: a new or replaced level (quantity 0 deletes).
                let q = next() % unit.saturating_mul(4);
                g.insert(key, q);
                if q == 0 {
                    m.remove(&key);
                } else {
                    m.insert(key, q);
                }
            }
            _ => check(
                &format!("remove({key})"),
                format!("{:?}", g.remove(key)),
                format!("{:?}", m.remove(&key)),
            )?,
        }
        if g.len() != m.len() {
            return Err(format!(
                "op #{i}: len glass {} != oracle {}",
                g.len(),
                m.len()
            ));
        }
    }
    same(&g, &m)
}

/// `Σ key·qty` over the first `lots` of `levels`, exact, then saturated to
/// `u64` (glass's estimator contract).
fn greedy<'a>(levels: impl Iterator<Item = &'a (u32, u64)>, mut lots: u64) -> u64 {
    let mut cost = 0u128;
    for &(k, q) in levels {
        if lots == 0 {
            break;
        }
        let take = q.min(lots);
        cost += k as u128 * take as u128;
        lots -= take;
    }
    cost.min(u64::MAX as u128) as u64
}

/// Market order of `size` against `m`, from the lowest key (or the highest,
/// `from_top`); returns `Σ key·qty` saturated to `u64`, as glass does.
fn execute(m: &mut BTreeMap<u32, u64>, mut size: u64, from_top: bool) -> u64 {
    let mut cost = 0u128;
    while size > 0 {
        let level = if from_top {
            m.last_entry()
        } else {
            m.first_entry()
        };
        let Some(mut level) = level else { break };
        let take = (*level.get()).min(size);
        cost += *level.key() as u128 * take as u128;
        size -= take;
        *level.get_mut() -= take;
        if *level.get() == 0 {
            level.remove();
        }
    }
    cost.min(u64::MAX as u128) as u64
}

fn same(g: &Glass, m: &BTreeMap<u32, u64>) -> Result<(), String> {
    if g.len() != m.len() {
        return Err(format!("len glass {} != oracle {}", g.len(), m.len()));
    }
    match g.iter().zip(m.iter()).position(|(x, (&k, &q))| x != (k, q)) {
        None => Ok(()),
        Some(i) => Err(format!(
            "level #{i}: glass {:?} != oracle {:?}",
            g.iter().nth(i),
            m.iter().nth(i)
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn both(updates: &[(Side, u32, u64)]) -> (BTreeBook, GlassBook) {
        let (mut b, mut g) = (BTreeBook::default(), GlassBook::default());
        for &(side, ticks, lots) in updates {
            b.set(side, Level { ticks, lots });
            g.set(side, Level { ticks, lots });
        }
        (b, g)
    }

    #[test]
    fn l2_semantics_by_hand() {
        use Side::*;
        let (mut b, mut g) = both(&[
            (Bid, 99, 5),
            (Bid, 98, 3),
            (Bid, 99, 7), // absolute: replaces 5
            (Bid, 97, 0), // deleting an absent level: no-op
            (Ask, 101, 4),
            (Ask, 102, 6),
            (Ask, 101, 0), // deletes
        ]);
        let lv = |ticks, lots| Level { ticks, lots };
        for book in [&mut b as &mut dyn OrderBook, &mut g] {
            assert_eq!(book.levels(), (2, 1));
            assert_eq!(book.best(Bid), Some(lv(99, 7)));
            assert_eq!(book.best(Ask), Some(lv(102, 6)));
            let mut out = Vec::new();
            book.top(Bid, 5, &mut out);
            assert_eq!(out, [lv(99, 7), lv(98, 3)], "bids best (highest) first");
            book.top(Ask, 5, &mut out);
            assert_eq!(out, [lv(102, 6)]);
            assert_eq!(book.market(Bid, 8), (7 * 99 + 98, 8));
            assert_eq!(book.market(Ask, 10), (6 * 102, 6), "fills what there is");
            assert_eq!(book.market(Ask, 0), (0, 0));
        }
        assert!(cross_check(&g, &b, true).is_ok());
    }

    /// 1000SATS-like numbers: prices of a few thousand ticks, sizes of 1e10
    /// lots, ~1e11 per side. `u32::MAX × lots` passes `u64` here, which the
    /// bid-side estimate must not trip over.
    #[test]
    fn huge_sizes_at_tiny_prices() {
        let mut ups = Vec::new();
        for i in 0..500u32 {
            let lots = 1_000_000_000 + (i as u64 * 97_654_321) % 50_000_000_000;
            ups.push((Side::Bid, 1263 - i, lots));
            ups.push((Side::Ask, 1264 + i * 7, lots / 3 + 1));
        }
        let (b, g) = both(&ups);
        for side in [Side::Bid, Side::Ask] {
            for lots in [1, 1 << 20, 4_000_000_000, 1 << 40, u64::MAX] {
                assert_eq!(g.market(side, lots), b.market(side, lots), "{lots} lots");
            }
        }
        assert!(cross_check(&g, &b, true).is_ok());
        // The walk by hand for the whole bid side, exactly.
        let exact: u128 = ups
            .iter()
            .filter(|u| u.0 == Side::Bid)
            .map(|&(_, t, q)| t as u128 * q as u128)
            .sum();
        assert_eq!(b.market(Side::Bid, u64::MAX).0 as u128, exact);
    }
}
