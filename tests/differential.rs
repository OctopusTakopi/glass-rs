//! Differential tests: Glass vs BTreeMap oracle.
//!
//! Covers the interaction of the trie tier with the preemption tier
//! (MAX_SIZE = 4096), the bounded hash-table lookup ("don't know" answers,
//! paper §5.2) and threshold maintenance (paper §4.5).

use glass_rs::Glass;
use std::collections::BTreeMap;

fn oracle_min(m: &BTreeMap<u32, u64>) -> Option<(u32, u64)> {
    m.iter().next().map(|(&k, &v)| (k, v))
}

fn oracle_max(m: &BTreeMap<u32, u64>) -> Option<(u32, u64)> {
    m.iter().next_back().map(|(&k, &v)| (k, v))
}

fn oracle_buy_cost(m: &BTreeMap<u32, u64>, mut target: u64) -> u64 {
    let mut cost = 0u64;
    for (&p, &q) in m.iter() {
        if target == 0 {
            break;
        }
        let take = q.min(target);
        cost += p as u64 * take;
        target -= take;
    }
    cost
}

fn oracle_buy_shares(m: &mut BTreeMap<u32, u64>, mut shares: u64) -> u64 {
    let mut cost = 0u64;
    while shares > 0 {
        let Some((&p, &q)) = m.iter().next() else {
            break;
        };
        if q <= shares {
            cost += p as u64 * q;
            shares -= q;
            m.remove(&p);
        } else {
            cost += p as u64 * shares;
            *m.get_mut(&p).unwrap() -= shares;
            shares = 0;
        }
    }
    cost
}

fn oracle_sell_cost(m: &BTreeMap<u32, u64>, mut target: u64) -> u64 {
    let mut proceeds = 0u64;
    for (&p, &q) in m.iter().rev() {
        if target == 0 {
            break;
        }
        let take = q.min(target);
        proceeds += p as u64 * take;
        target -= take;
    }
    proceeds
}

fn oracle_sell_shares(m: &mut BTreeMap<u32, u64>, mut shares: u64) -> u64 {
    let mut proceeds = 0u64;
    while shares > 0 {
        let Some((&p, &q)) = m.iter().next_back() else {
            break;
        };
        if q <= shares {
            proceeds += p as u64 * q;
            shares -= q;
            m.remove(&p);
        } else {
            proceeds += p as u64 * shares;
            *m.get_mut(&p).unwrap() -= shares;
            shares = 0;
        }
    }
    proceeds
}

/// Deterministic xorshift so failures are reproducible.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

fn check_all(glass: &Glass, oracle: &BTreeMap<u32, u64>, universe: &[u32], ctx: &str) {
    assert_eq!(glass.min(), oracle_min(oracle), "min mismatch ({ctx})");
    assert_eq!(glass.max(), oracle_max(oracle), "max mismatch ({ctx})");
    assert_eq!(glass.len(), oracle.len(), "len mismatch ({ctx})");
    assert_eq!(glass.is_empty(), oracle.is_empty(), "is_empty ({ctx})");
    let mine: Vec<(u32, u64)> = glass.iter().collect();
    let theirs: Vec<(u32, u64)> = oracle.iter().map(|(&k, &v)| (k, v)).collect();
    assert_eq!(mine, theirs, "iter mismatch ({ctx})");
    for &k in universe {
        assert_eq!(
            glass.get(k),
            oracle.get(&k).copied(),
            "get({k}) mismatch ({ctx})"
        );
    }
}

/// Paper §5.2: chains longer than J=5 must answer "don't know" and fall back
/// to trie descent. Keys at stride 2^18 share partial-key low bits, so with
/// HT_SIZE = 4096 they all collide into one bucket.
#[test]
fn ht_chain_overflow_keys_stay_visible() {
    let mut glass = Glass::new();
    let mut oracle = BTreeMap::new();
    let keys: Vec<u32> = (0..16u32).map(|i| i << 18).collect();
    for (i, &k) in keys.iter().enumerate() {
        glass.insert(k, i as u64 + 1);
        oracle.insert(k, i as u64 + 1);
    }
    check_all(&glass, &oracle, &keys, "after colliding inserts");

    // update_value goes through the same lookup path
    for &k in &keys {
        assert!(
            glass.update_value(k, |v| *v += 10),
            "update_value({k}) failed to find key"
        );
        *oracle.get_mut(&k).unwrap() += 10;
    }
    check_all(&glass, &oracle, &keys, "after colliding updates");

    // removal must find the keys too
    for (i, &k) in keys.iter().enumerate() {
        assert_eq!(
            glass.remove(k),
            oracle.remove(&k),
            "remove({k}) mismatch (i={i})"
        );
    }
    assert_eq!(glass.min(), None);
    assert_eq!(glass.glass_size(), 0);
}

/// Paper §4.5: the preemption threshold must be maintained eagerly. When the
/// glass is full and a better key evicts the current worst into the preempt
/// map, the threshold must drop immediately, or lookups misroute.
#[test]
fn thres_stays_correct_after_eviction() {
    let mut glass = Glass::new();
    let mut oracle = BTreeMap::new();

    // Fill the glass with 4096 even keys: 0, 2, ..., 8190.
    for i in 0..4096u32 {
        glass.insert(i * 2, 1);
        oracle.insert(i * 2, 1);
    }
    // One high key goes to the preempt map; thres becomes 100_000 once observed.
    glass.insert(100_000, 7);
    oracle.insert(100_000, 7);
    assert_eq!(glass.get(100_000), Some(7)); // forces threshold refresh

    // Insert a better key: glass is full, so worst key 8190 must be evicted
    // into the preempt map and the threshold must drop to 8190 NOW.
    glass.insert(1, 9);
    oracle.insert(1, 9);

    // The evicted key must still be visible through the public API.
    assert_eq!(glass.get(8190), Some(1), "evicted key lost (stale thres)");
    assert_eq!(glass.get(1), Some(9));
    assert_eq!(glass.get(100_000), Some(7));

    // Re-inserting the evicted key must not create a duplicate across tiers.
    glass.insert(8190, 5);
    oracle.insert(8190, 5);
    assert_eq!(glass.get(8190), Some(5));

    // Drain from the bottom; if 8190 was duplicated, a stale value resurfaces.
    for _ in 0..2000 {
        let g = glass.remove_by_index(0);
        let (&k, &v) = oracle.iter().next().unwrap();
        oracle.remove(&k);
        assert_eq!(g, Some((k, v)), "remove_by_index diverged");
    }
    let keys: Vec<u32> = oracle.keys().copied().collect();
    check_all(&glass, &oracle, &keys, "after drain");
}

/// The paper's adjust() deletes a price level when its amount reaches zero.
/// update_value must not leave a zero value behind with a set mask bit.
#[test]
fn update_value_to_zero_removes_level() {
    let mut glass = Glass::new();
    glass.insert(10, 5);
    glass.insert(20, 7);
    assert!(glass.update_value(10, |v| *v = 0));
    assert_eq!(glass.get(10), None);
    assert_eq!(glass.glass_size(), 1);
    assert_eq!(glass.min(), Some((20, 7)));
    assert_eq!(glass.compute_buy_cost(7), 140);
}

#[test]
fn boundary_keys() {
    let mut glass = Glass::new();
    glass.insert(0, 3);
    glass.insert(u32::MAX, 4);
    assert_eq!(glass.get(0), Some(3));
    assert_eq!(glass.get(u32::MAX), Some(4));
    assert_eq!(glass.min(), Some((0, 3)));
    assert_eq!(glass.max(), Some((u32::MAX, 4)));
    assert_eq!(glass.remove(0), Some(3));
    assert_eq!(glass.min(), Some((u32::MAX, 4)));
    assert_eq!(glass.remove(u32::MAX), Some(4));
    assert_eq!(glass.min(), None);
    assert_eq!(glass.max(), None);
}

/// clear() must fully reset routing state, not just empty the containers.
#[test]
fn clear_resets_routing() {
    let mut glass = Glass::new();
    for i in 0..5000u32 {
        glass.insert(i, 1); // crosses the preemption boundary
    }
    assert_eq!(glass.len(), 5000);
    glass.clear();
    assert_eq!(glass.len(), 0);
    assert!(glass.is_empty());
    assert_eq!(glass.min(), None);
    assert_eq!(glass.iter().next(), None);

    // Reuse after clear must behave like a fresh glass.
    let mut oracle = BTreeMap::new();
    for i in 0..5000u32 {
        glass.insert(i * 3, (i as u64 % 7) + 1);
        oracle.insert(i * 3, (i as u64 % 7) + 1);
    }
    let keys: Vec<u32> = oracle.keys().copied().collect();
    check_all(&glass, &oracle, &keys, "after clear+refill");
    assert_eq!(
        glass.buy_shares(u64::MAX),
        oracle_buy_shares(&mut oracle, u64::MAX)
    );
}

/// Sells must drain the overflow tier (highest prices) before the trie, and
/// stay exact across the tier boundary.
#[test]
fn sell_across_tiers() {
    let mut glass = Glass::new();
    let mut oracle = BTreeMap::new();
    // 6000 levels: 4096 lowest in the trie, the rest preempted.
    for i in 0..6000u32 {
        glass.insert(i * 2 + 1, (i as u64 % 9) + 1);
        oracle.insert(i * 2 + 1, (i as u64 % 9) + 1);
    }
    assert_eq!(glass.len(), 6000);

    // Small sell: hits only the overflow tier.
    assert_eq!(glass.sell_shares(37), oracle_sell_shares(&mut oracle, 37));
    assert_eq!(
        glass.max(),
        oracle.iter().next_back().map(|(&k, &v)| (k, v))
    );

    // Estimation must agree at every depth including across the boundary.
    for t in [10u64, 5_000, 12_000, 40_000, u64::MAX] {
        assert_eq!(
            glass.compute_sell_cost(t),
            oracle_sell_cost(&oracle, t),
            "compute_sell_cost({t})"
        );
    }

    // Deep sell crossing from the map tier into the trie.
    assert_eq!(
        glass.sell_shares(20_000),
        oracle_sell_shares(&mut oracle, 20_000)
    );
    let keys: Vec<u32> = oracle.keys().copied().collect();
    check_all(&glass, &oracle, &keys, "after deep sell");

    // Interleave sells and buys until empty.
    loop {
        let g = glass.sell_shares(700);
        let o = oracle_sell_shares(&mut oracle, 700);
        assert_eq!(g, o, "interleaved sell");
        let g = glass.buy_shares(300);
        let o = oracle_buy_shares(&mut oracle, 300);
        assert_eq!(g, o, "interleaved buy");
        if oracle.is_empty() {
            break;
        }
    }
    assert!(glass.is_empty());
}

/// BTreeMap-style conveniences behave like their std counterparts.
#[test]
fn btreemap_like_api() {
    let mut glass = Glass::new();
    let mut oracle = BTreeMap::new();
    for i in 0..500u32 {
        glass.insert(i * 7 + 3, i as u64 + 1);
        oracle.insert(i * 7 + 3, i as u64 + 1);
    }

    assert!(glass.contains_key(3));
    assert!(!glass.contains_key(4));
    assert_eq!(glass.get_key_value(10), Some((10, 2)));
    assert_eq!(glass.first_key_value(), Some((3, 1)));
    assert_eq!(glass.last_key_value(), Some((499 * 7 + 3, 500)));

    // next/prev navigation, including edges.
    assert_eq!(glass.next_level(0), Some((3, 1)));
    assert_eq!(glass.next_level(3), Some((10, 2)));
    assert_eq!(glass.next_level(u32::MAX), None);
    assert_eq!(glass.prev_level(3), None);
    assert_eq!(glass.prev_level(10), Some((3, 1)));
    assert_eq!(glass.prev_level(u32::MAX), Some((499 * 7 + 3, 500)));

    // keys/values ordering.
    let ks: Vec<u32> = glass.keys().take(3).collect();
    assert_eq!(ks, vec![3, 10, 17]);
    let vs: Vec<u64> = glass.values().take(3).collect();
    assert_eq!(vs, vec![1, 2, 3]);

    // range with all bound shapes.
    use std::ops::Bound::{Excluded, Included};
    let cases: Vec<(std::ops::Bound<u32>, std::ops::Bound<u32>)> = vec![
        (Included(10), Excluded(100)),
        (Excluded(10), Included(100)),
        (Included(0), Included(u32::MAX)),
        (Included(101), Excluded(101)),
        (Excluded(u32::MAX), std::ops::Bound::Unbounded),
    ];
    for (lo, hi) in cases {
        let mine: Vec<(u32, u64)> = glass.range((lo, hi)).collect();
        let theirs: Vec<(u32, u64)> = oracle.range((lo, hi)).map(|(&k, &v)| (k, v)).collect();
        assert_eq!(mine, theirs, "range({lo:?}, {hi:?})");
    }

    // pop_first / pop_last.
    assert_eq!(glass.pop_first(), oracle.pop_first());
    assert_eq!(glass.pop_last(), oracle.pop_last());

    // retain: keep even quantities only.
    glass.retain(|_, v| v % 2 == 0);
    oracle.retain(|_, v| *v % 2 == 0);
    assert_eq!(glass.len(), oracle.len());
    let mine: Vec<(u32, u64)> = glass.iter().collect();
    let theirs: Vec<(u32, u64)> = oracle.iter().map(|(&k, &v)| (k, v)).collect();
    assert_eq!(mine, theirs, "after retain");

    // split_off.
    let split_key = 1000;
    let upper = glass.split_off(split_key);
    let upper_oracle = oracle.split_off(&split_key);
    assert_eq!(
        upper.iter().collect::<Vec<_>>(),
        upper_oracle
            .iter()
            .map(|(&k, &v)| (k, v))
            .collect::<Vec<_>>(),
        "split_off upper"
    );
    assert_eq!(
        glass.iter().collect::<Vec<_>>(),
        oracle.iter().map(|(&k, &v)| (k, v)).collect::<Vec<_>>(),
        "split_off lower"
    );

    // owned IntoIterator drains ascending.
    let drained: Vec<(u32, u64)> = upper.into_iter().collect();
    assert_eq!(
        drained,
        upper_oracle
            .iter()
            .map(|(&k, &v)| (k, v))
            .collect::<Vec<_>>()
    );
}

/// top_levels must agree with the oracle prefix through the dense (AVX
/// compress) path, the sparse (scalar) path, and the overflow-tier spill.
#[test]
fn top_levels_snapshot() {
    let mut buf = Vec::new();

    // Dense leaves: contiguous keys fill 64-slot leaves completely.
    let mut glass = Glass::new();
    let mut oracle = BTreeMap::new();
    for i in 0..300u32 {
        glass.insert(1000 + i, i as u64 + 1);
        oracle.insert(1000 + i, i as u64 + 1);
    }
    for depth in [1usize, 8, 25, 64, 100, 300, 500] {
        glass.top_levels(depth, &mut buf);
        let expected: Vec<(u32, u64)> = oracle.iter().take(depth).map(|(&k, &v)| (k, v)).collect();
        assert_eq!(buf, expected, "dense top_levels({depth})");
    }

    // Sparse leaves: strided keys, few bits per leaf.
    let mut glass = Glass::new();
    let mut oracle = BTreeMap::new();
    for i in 0..200u32 {
        glass.insert(i * 97, i as u64 + 1);
        oracle.insert(i * 97, i as u64 + 1);
    }
    for depth in [1usize, 25, 200] {
        glass.top_levels(depth, &mut buf);
        let expected: Vec<(u32, u64)> = oracle.iter().take(depth).map(|(&k, &v)| (k, v)).collect();
        assert_eq!(buf, expected, "sparse top_levels({depth})");
    }

    // Spill into the overflow tier: n beyond the 4096-level trie.
    let mut glass = Glass::new();
    let mut oracle = BTreeMap::new();
    for i in 0..5000u32 {
        glass.insert(i, 1);
        oracle.insert(i, 1);
    }
    glass.top_levels(4500, &mut buf);
    let expected: Vec<(u32, u64)> = oracle.iter().take(4500).map(|(&k, &v)| (k, v)).collect();
    assert_eq!(buf, expected, "spill top_levels(4500)");
    assert_eq!(glass.top_levels(0, &mut buf), 0);
    assert!(buf.is_empty());
}

/// FromIterator/Extend round-trip through iter().
#[test]
fn from_iterator_round_trip() {
    let src: Vec<(u32, u64)> = (0..1000u32).map(|i| (i * 5, i as u64 + 1)).collect();
    let glass: Glass = src.iter().copied().collect();
    assert_eq!(glass.len(), 1000);
    let collected: Vec<(u32, u64)> = glass.iter().collect();
    assert_eq!(collected, src);
}

/// Randomized differential test crossing the preemption boundary (> 4096 live
/// keys) with mixed operations.
#[test]
fn random_ops_match_btreemap() {
    let mut rng = Rng(0x9E3779B97F4A7C15);
    let mut glass = Glass::new();
    let mut oracle: BTreeMap<u32, u64> = BTreeMap::new();

    // Key universe mixes: dense band (locality), sparse band (crosses
    // preemption), and colliding stride keys (HT chain overflow).
    let key_for = |r: u64| -> u32 {
        match r % 10 {
            0..=5 => 1000 + (r / 10 % 3000) as u32, // dense band
            6..=8 => ((r / 10) % 8000) as u32 * 16, // wide band
            _ => (((r / 10) % 32) as u32) << 18,    // colliding stride
        }
    };

    for step in 0..200_000u64 {
        let r = rng.next();
        let key = key_for(r);
        match r % 100 {
            0..=39 => {
                let v = rng.below(1000) + 1;
                glass.insert(key, v);
                oracle.insert(key, v);
            }
            40..=59 => {
                assert_eq!(
                    glass.remove(key),
                    oracle.remove(&key),
                    "remove({key}) mismatch at step {step}"
                );
            }
            60..=74 => {
                assert_eq!(
                    glass.get(key),
                    oracle.get(&key).copied(),
                    "get({key}) mismatch at step {step}"
                );
            }
            75..=84 => {
                let updated = glass.update_value(key, |v| *v += 3);
                if updated {
                    *oracle.get_mut(&key).expect("update_value ghost hit") += 3;
                } else {
                    assert!(!oracle.contains_key(&key), "update_value missed {key}");
                }
            }
            85..=89 => {
                assert_eq!(glass.min(), oracle_min(&oracle), "min at step {step}");
                assert_eq!(glass.max(), oracle_max(&oracle), "max at step {step}");
            }
            90..=93 => {
                let n = oracle.len();
                if n > 0 {
                    let k = (rng.below(n as u64)) as usize;
                    let expected = oracle.keys().nth(k).copied().map(|key| {
                        let v = oracle.remove(&key).unwrap();
                        (key, v)
                    });
                    assert_eq!(
                        glass.remove_by_index(k),
                        expected,
                        "remove_by_index({k}) at step {step}"
                    );
                }
            }
            94 => {
                let target = rng.below(5000);
                assert_eq!(
                    glass.compute_buy_cost(target),
                    oracle_buy_cost(&oracle, target),
                    "compute_buy_cost({target}) at step {step}"
                );
                assert_eq!(
                    glass.compute_sell_cost(target),
                    oracle_sell_cost(&oracle, target),
                    "compute_sell_cost({target}) at step {step}"
                );
            }
            95 => {
                let shares = rng.below(3000);
                assert_eq!(
                    glass.buy_shares(shares),
                    oracle_buy_shares(&mut oracle, shares),
                    "buy_shares({shares}) at step {step}"
                );
            }
            96 => {
                let shares = rng.below(3000);
                assert_eq!(
                    glass.sell_shares(shares),
                    oracle_sell_shares(&mut oracle, shares),
                    "sell_shares({shares}) at step {step}"
                );
            }
            97 => {
                use std::ops::Bound::{Excluded, Unbounded};
                assert_eq!(
                    glass.next_level(key),
                    oracle
                        .range((Excluded(key), Unbounded))
                        .next()
                        .map(|(&k, &v)| (k, v)),
                    "next_level({key}) at step {step}"
                );
                assert_eq!(
                    glass.prev_level(key),
                    oracle.range(..key).next_back().map(|(&k, &v)| (k, v)),
                    "prev_level({key}) at step {step}"
                );
            }
            98 => {
                assert_eq!(
                    glass.pop_first(),
                    oracle.pop_first(),
                    "pop_first at step {step}"
                );
                assert_eq!(
                    glass.pop_last(),
                    oracle.pop_last(),
                    "pop_last at step {step}"
                );
            }
            _ => {
                let hi = key.saturating_add(rng.below(4000) as u32);
                let mine: Vec<(u32, u64)> = glass.range(key..hi).take(50).collect();
                let theirs: Vec<(u32, u64)> = oracle
                    .range(key..hi)
                    .take(50)
                    .map(|(&k, &v)| (k, v))
                    .collect();
                assert_eq!(mine, theirs, "range({key}..{hi}) at step {step}");
                assert_eq!(
                    glass.contains_key(key),
                    oracle.contains_key(&key),
                    "contains_key({key}) at step {step}"
                );
                let depth = (rng.below(60) + 1) as usize;
                let mut buf = Vec::new();
                glass.top_levels(depth, &mut buf);
                let expected: Vec<(u32, u64)> =
                    oracle.iter().take(depth).map(|(&k, &v)| (k, v)).collect();
                assert_eq!(buf, expected, "top_levels({depth}) at step {step}");
            }
        }
    }

    // Final full sweep.
    let keys: Vec<u32> = oracle.keys().copied().collect();
    check_all(&glass, &oracle, &keys, "final");
    assert_eq!(glass.min(), oracle_min(&oracle));

    // Large targets exercise the whole-leaf (vectorized) estimation path
    // across many leaves and into the preempt tail.
    for t in [10_000u64, 300_000, 10_000_000, u64::MAX] {
        assert_eq!(
            glass.compute_buy_cost(t),
            oracle_buy_cost(&oracle, t),
            "compute_buy_cost({t}) deep sweep"
        );
    }

    // Drain completely via buy_shares.
    let full = oracle.values().sum::<u64>();
    assert_eq!(
        glass.buy_shares(u64::MAX),
        oracle_buy_shares(&mut oracle, u64::MAX),
        "full drain"
    );
    let _ = full;
    assert_eq!(glass.min(), None);
    assert_eq!(glass.glass_size(), 0);
}
