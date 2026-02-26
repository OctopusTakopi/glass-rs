#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let glass = Glass::new();
        assert_eq!(glass.glass_size(), 0);
        assert_eq!(glass.arena.len(), 1);
        assert_eq!(glass.root, 0);
        assert!(unsafe { &*glass.preempt.get() }.is_empty());
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
        for i in 0..(4096 + 10) {
            glass.insert(i as u32, 1);
        }
        assert_eq!(glass.glass_size(), 4096);
        assert!(!unsafe { &*glass.preempt.get() }.is_empty());
        glass.remove(0); 
        assert_eq!(glass.glass_size(), 4096);
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
        let glass = Glass::new();
        let mask = 0b0001_0010; 
        assert_eq!(glass.find_next_set_bit(mask, 0), Some(1));
        assert_eq!(glass.find_next_set_bit(mask, 2), Some(4));
        assert_eq!(glass.find_next_set_bit(mask, 5), None);
    }

    #[test]
    fn test_find_prev_set_bit() {
        let glass = Glass::new();
        let mask = 0b0001_0010; 
        assert_eq!(glass.find_prev_set_bit(mask, 64), Some(4));
        assert_eq!(glass.find_prev_set_bit(mask, 4), Some(1));
        assert_eq!(glass.find_prev_set_bit(mask, 1), None);
    }
}
