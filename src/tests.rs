#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let glass = Glass::new();
        assert_eq!(glass.glass_size(), 0);
        assert_eq!(glass.arena.len(), 1);
        assert!(glass.preempt.is_empty());
    }

    #[test]
    fn test_insert_and_get() {
        let mut glass = Glass::new();
        glass.insert(123, 999999999999);
        assert_eq!(glass.get(123), Some(999999999999));
        assert_eq!(glass.glass_size(), 1);
        glass.insert(456, 888888888888);
        assert_eq!(glass.get(456), Some(888888888888));
        assert_eq!(glass.glass_size(), 2);
        glass.insert(123, 0);
        assert_eq!(glass.get(123), None);
        assert_eq!(glass.glass_size(), 1);
    }

    #[test]
    fn test_remove_by_index() {
        let mut glass = Glass::new();
        glass.insert(10, 100);
        glass.insert(30, 300);
        glass.insert(20, 200);
        glass.insert(5, 50);

        assert_eq!(glass.glass_size(), 4);
        assert_eq!(glass.min(), Some((5, 50)));

        assert_eq!(glass.remove_by_index(1), Some((10, 100)));
        assert_eq!(glass.glass_size(), 3);
        assert_eq!(glass.get(10), None);

        assert_eq!(glass.remove_by_index(0), Some((5, 50)));
        assert_eq!(glass.glass_size(), 2);
        assert_eq!(glass.get(5), None);
        assert_eq!(glass.min(), Some((20, 200)));

        assert_eq!(glass.remove_by_index(1), Some((30, 300)));
        assert_eq!(glass.glass_size(), 1);
        assert_eq!(glass.get(30), None);
        assert_eq!(glass.max(), Some((20, 200)));

        assert_eq!(glass.remove_by_index(0), Some((20, 200)));
        assert_eq!(glass.glass_size(), 0);
        assert!(glass.min().is_none());

        assert_eq!(glass.remove_by_index(0), None);
    }

    #[test]
    fn test_update_value() {
        let mut glass = Glass::new();
        glass.insert(123, 100);
        let updated = glass.update_value(123, |v| *v += 50);
        assert!(updated);
        assert_eq!(glass.get(123), Some(150));
        let not_updated = glass.update_value(999, |_| {});
        assert!(!not_updated);
    }

    #[test]
    fn test_remove() {
        let mut glass = Glass::new();
        glass.insert(123, 999999999999);
        let removed = glass.remove(123);
        assert_eq!(removed, Some(999999999999));
        assert_eq!(glass.get(123), None);
        assert_eq!(glass.glass_size(), 0);
        let none_removed = glass.remove(123);
        assert_eq!(none_removed, None);
    }

    #[test]
    fn test_min_and_max() {
        let mut glass = Glass::new();
        glass.insert(10, 500);
        glass.insert(20, 600);
        glass.insert(30, 700);
        glass.insert(40, 800);
        assert_eq!(glass.min(), Some((10, 500)));
        assert_eq!(glass.max(), Some((40, 800)));
        glass.remove(10);
        assert_eq!(glass.min(), Some((20, 600)));
        glass.remove(40);
        assert_eq!(glass.max(), Some((30, 700)));
    }

    #[test]
    fn test_restructure() {
        let mut glass = Glass::new();
        let total = 4096 + 100;
        for i in 0..total {
            glass.insert(i as u32, 1);
        }
        assert_eq!(glass.glass_size(), 4096);
        assert_eq!(glass.preempt.len(), 100);
        // Within the refill band, removals leave the trie short.
        for k in 0..(REFILL_BATCH - 1) as u32 {
            glass.remove(k);
        }
        assert_eq!(glass.glass_size(), 4096 - (REFILL_BATCH - 1));
        assert_eq!(glass.preempt.len(), 100);
        // The removal that makes it REFILL_BATCH short refills it to MAX_SIZE
        // with the lowest preempt levels.
        glass.remove(REFILL_BATCH as u32 - 1);
        assert_eq!(glass.glass_size(), 4096);
        assert_eq!(glass.preempt.len(), 100 - REFILL_BATCH);
        assert_eq!(glass.preempt_keys.len(), glass.preempt.len());
        assert_eq!(glass.thres, (4096 + REFILL_BATCH) as u32);
        for k in REFILL_BATCH as u32..total as u32 {
            assert_eq!(glass.get(k), Some(1), "key {k} lost across the refill");
        }
    }

    // A sweep that drains the trie must not trigger an unbounded refill:
    // each call moves at most REFILL_BATCH preempt levels back, and later
    // calls keep topping the trie up. No level is lost or reordered.
    #[test]
    fn test_refill_is_bounded_after_sweep() {
        let mut glass = Glass::new();
        for k in 0..6000u32 {
            glass.insert(k, 1);
        }
        assert_eq!(glass.glass_size(), MAX_SIZE);
        // Consumes the whole trie, then 4 levels straight from preempt.
        assert_eq!(glass.buy_shares(4100), (0..4100u64).sum::<u64>());
        assert_eq!(glass.glass_size(), REFILL_BATCH);
        assert_eq!(glass.len(), 6000 - 4100);
        assert_eq!(glass.min(), Some((4100, 1)));
        // Every later mutation that finds the trie short tops it up by at
        // most REFILL_BATCH, whichever tier it touched.
        let before = glass.glass_size();
        glass.remove(4100); // a trie level
        assert_eq!(glass.glass_size(), before - 1 + REFILL_BATCH);
        let before = glass.glass_size();
        glass.remove(5999); // a preempt level
        assert_eq!(glass.glass_size(), before + REFILL_BATCH);
        let before = glass.glass_size();
        glass.insert(7000, 1); // lands in preempt
        assert_eq!(glass.glass_size(), before + REFILL_BATCH);
        let want: Vec<(u32, u64)> = (4101..5999u32).chain([7000]).map(|k| (k, 1)).collect();
        assert_eq!(glass.iter().collect::<Vec<_>>(), want);
    }

    #[test]
    fn test_buy_shares() {
        let mut glass = Glass::new();
        glass.insert(10, 500);
        glass.insert(20, 600);
        let cost = glass.buy_shares(700);
        assert_eq!(cost, (10 * 500) + (20 * 200));
        assert_eq!(glass.get(10), None);
        assert_eq!(glass.get(20), Some(400));
        assert_eq!(glass.min_key.get(), 20);
    }

    #[test]
    fn test_compute_buy_cost() {
        let mut glass = Glass::new();
        glass.insert(10, 500);
        glass.insert(20, 600);
        glass.insert(30, 700);
        glass.insert(40, 800);
        let cost = glass.compute_buy_cost(1000);
        assert_eq!(cost, (10 * 500) + (20 * 500));
        let full_cost = glass.compute_buy_cost(2600);
        assert_eq!(full_cost, (10 * 500) + (20 * 600) + (30 * 700) + (40 * 800));
    }

    #[test]
    fn test_glass_insert() {
        let mut glass = Glass::new();
        glass.glass_insert(123, 999);
        assert_eq!(glass.glass_get(123), Some(999));
        assert_eq!(glass.min_key.get(), 123);
        assert_eq!(glass.max_key.get(), 123);
    }

    #[test]
    fn test_glass_get() {
        let mut glass = Glass::new();
        glass.glass_insert(123, 999);
        assert_eq!(glass.glass_get(123), Some(999));
        assert_eq!(glass.glass_get(456), None);
    }

    #[test]
    fn test_glass_get_mut() {
        let mut glass = Glass::new();
        glass.glass_insert(123, 999);
        if let Some(v) = glass.glass_get_mut(123) {
            *v = 1000;
        }
        assert_eq!(glass.glass_get(123), Some(1000));
        assert!(glass.glass_get_mut(456).is_none());
    }

    #[test]
    fn test_glass_remove() {
        let mut glass = Glass::new();
        glass.glass_insert(123, 999);
        assert_eq!(glass.glass_size(), 1);
        let removed = glass.glass_remove(123);
        assert_eq!(removed, Some(999));
        assert_eq!(glass.glass_size(), 0);
        assert_eq!(glass.glass_get(123), None);
        assert_eq!(glass.min_key.get(), 4294967295);
        assert_eq!(glass.max_key.get(), 0);
    }

    #[test]
    fn test_glass_min() {
        let mut glass = Glass::new();
        glass.glass_insert(20, 600);
        glass.glass_insert(10, 500);
        assert_eq!(glass.glass_min(), Some((10, 500)));
    }

    #[test]
    fn test_glass_max() {
        let mut glass = Glass::new();
        glass.glass_insert(20, 600);
        glass.glass_insert(30, 700);
        assert_eq!(glass.glass_max(), Some((30, 700)));
    }

    #[test]
    fn test_glass_find_extreme() {
        let mut glass = Glass::new();
        glass.glass_insert(10, 500);
        glass.glass_insert(40, 800);
        assert_eq!(glass.glass_find_extreme(true), Some((10, 500)));
        assert_eq!(glass.glass_find_extreme(false), Some((40, 800)));
    }

    #[test]
    fn test_glass_compute_buy_cost() {
        let mut glass = Glass::new();
        glass.glass_insert(10, 500);
        glass.glass_insert(20, 600);
        let cost = glass.compute_buy_cost(700);
        assert_eq!(cost, (10 * 500) + (20 * 200));
        assert_eq!(glass.min_key.get(), 10);
    }

    #[test]
    fn test_insert_invariant_bug_repro() {
        let mut glass = Glass::new();
        for i in 0..4096 {
            glass.insert(i as u32 * 2, 1);
        }
        glass.insert(9000, 1);
        assert_eq!(glass.get(9000), Some(1));
    }

    #[test]
    fn test_find_next_set_bit() {
        let mask = 0b0001_0010;
        assert_eq!(find_next_set_bit(mask, 0), Some(1));
        assert_eq!(find_next_set_bit(mask, 2), Some(4));
        assert_eq!(find_next_set_bit(mask, 5), None);
    }

    #[test]
    fn test_find_prev_set_bit() {
        let mask = 0b0001_0010;
        assert_eq!(find_prev_set_bit(mask, 64), Some(4));
        assert_eq!(find_prev_set_bit(mask, 4), Some(1));
        assert_eq!(find_prev_set_bit(mask, 1), None);
    }

    // Every leaf-sum implementation must agree with the exact u128 answer:
    // `Some((sum, min(weighted, u64::MAX)))` when sum(qty) fits in u64, else
    // `None`. The machine running the tests normally takes only one of the
    // SIMD paths, so each is forced here.
    #[test]
    fn test_leaf_sums_paths_agree() {
        fn exact(values: &[u64; NUM_CHILDREN]) -> Option<(u64, u64)> {
            let qty: u128 = values.iter().map(|&v| v as u128).sum();
            let w: u128 = values.iter().enumerate().map(|(i, &v)| i as u128 * v as u128).sum();
            let qty = u64::try_from(qty).ok()?;
            Some((qty, u64::try_from(w).unwrap_or(u64::MAX)))
        }
        let mut s = 0x2545F4914F6CDD1Du64;
        let mut next = || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        };
        let mut glass = Glass::new();
        let has_avx512 = glass.has_avx512;
        let has_avx2 = glass.has_avx2;
        for round in 0..4000 {
            let mut values = [0u64; NUM_CHILDREN];
            for v in values.iter_mut() {
                let r = next();
                *v = match (r % 8, round % 4) {
                    (0..=3, _) => 0,
                    (_, 0) => r >> 40,                          // small: fast path
                    (_, 1) => (1 << 52) - 1 - (r >> 60),        // just below the bound
                    (_, 2) => (1 << 52) + (r >> 20),            // just above the bound
                    _ => r,                                      // anything
                };
            }
            let want = exact(&values);
            assert_eq!(leaf_sums_wide(&values), want, "wide, round {round}");
            glass.has_avx512 = false;
            glass.has_avx2 = false;
            assert_eq!(glass.leaf_sums(&values), want, "scalar, round {round}");
            if has_avx2 {
                glass.has_avx2 = true;
                assert_eq!(glass.leaf_sums(&values), want, "avx2, round {round}");
            }
            if has_avx512 {
                glass.has_avx512 = true;
                assert_eq!(glass.leaf_sums(&values), want, "avx512, round {round}");
            }
        }
    }
}
