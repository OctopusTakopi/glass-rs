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
            0..=5 => 1000 + (r / 10 % 3000) as u32,       // dense band
            6..=8 => ((r / 10) % 8000) as u32 * 16,        // wide band
            _ => (((r / 10) % 32) as u32) << 18,           // colliding stride
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
            94..=96 => {
                let target = rng.below(5000);
                assert_eq!(
                    glass.compute_buy_cost(target),
                    oracle_buy_cost(&oracle, target),
                    "compute_buy_cost({target}) at step {step}"
                );
            }
            _ => {
                let shares = rng.below(3000);
                assert_eq!(
                    glass.buy_shares(shares),
                    oracle_buy_shares(&mut oracle, shares),
                    "buy_shares({shares}) at step {step}"
                );
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
