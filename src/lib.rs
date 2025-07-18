use ahash::AHashMap as HashMap;
use std::arch::x86_64::*;
use std::array;
use std::cell::{Cell, UnsafeCell};

const BITS_PER_LEVEL: usize = 6; // Radix: 64 children per node
const NUM_CHILDREN: usize = 1 << BITS_PER_LEVEL;
const KEY_BITS: usize = 32;
const LAST_BITS: usize = if KEY_BITS.is_multiple_of(BITS_PER_LEVEL) {
    BITS_PER_LEVEL
} else {
    KEY_BITS % BITS_PER_LEVEL
};
const LAST_MASK: u64 = (1 << LAST_BITS) - 1;
const NUM_LEVELS: usize = KEY_BITS.div_ceil(BITS_PER_LEVEL);
const MAX_SIZE: usize = 4096;
const ARENA_CAPACITY: usize = 16384;

struct GlassNode {
    mask: u64,
    value: Option<u64>,
    count: u32, // New field: Number of keys in this subtree
    _padding: u32,
    children: [Option<usize>; NUM_CHILDREN],
}

impl GlassNode {
    fn new() -> Self {
        GlassNode {
            mask: 0,
            value: None,
            count: 0, // Initialize count to 0
            _padding: 0,
            children: array::from_fn(|_| None),
        }
    }
}

pub struct Glass {
    // === Hot frequently accessed fields ===
    root: usize,                        // 8 bytes
    cached_d: Cell<usize>,              // 8
    cached_last_key: Cell<Option<u32>>, // 8

    // Bounds and thresholds
    min_key: Cell<u32>,     // 4
    preempt_min: Cell<u32>, // 4
    thres: Cell<u32>,       // 4
    max_key: Cell<u32>,     // 4
    preempt_max: Cell<u32>, // 4

    // Flags: manually packed
    preempt_bounds_valid: Cell<bool>, // 1
    has_bmi2: bool,                   // 1
    has_bmi1: bool,                   // 1
    has_lzcnt: bool,                  // 1
    _padding_flags: [u8; 4],          // pad to align next 8-byte field

    // Leaf node tracking
    min_leaf: Cell<Option<usize>>, // 16
    max_leaf: Cell<Option<usize>>, // 16

    // === Larger cold/cached structures ===
    cache: UnsafeCell<HashMap<u32, usize>>,       // 8
    preempt: UnsafeCell<HashMap<u32, u64>>,       // 8
    cached_path: UnsafeCell<[usize; NUM_LEVELS]>, // 8

    arena: Vec<GlassNode>,  // 24
    free_list: Vec<usize>, // 24
}

impl Default for Glass {
    fn default() -> Self {
        Self::new()
    }
}

impl Glass {
    pub fn new() -> Self {
        let mut arena = Vec::with_capacity(ARENA_CAPACITY);
        arena.push(GlassNode::new());
        let mut cached_path = [0; NUM_LEVELS];
        cached_path[0] = 0;
        Glass {
            arena,
            free_list: Vec::new(),
            root: 0,
            cache: UnsafeCell::new(HashMap::new()),
            cached_path: UnsafeCell::new(cached_path),
            cached_d: Cell::new(0),
            // size: Cell::new(0), // Removed
            min_leaf: Cell::new(None),
            max_leaf: Cell::new(None),
            preempt: UnsafeCell::new(HashMap::new()),
            preempt_bounds_valid: Cell::new(true),

            cached_last_key: Cell::new(None),

            min_key: Cell::new(u32::MAX),
            preempt_min: Cell::new(u32::MAX),
            thres: Cell::new(u32::MAX),
            max_key: Cell::new(0),
            preempt_max: Cell::new(0),

            has_bmi2: std::is_x86_feature_detected!("bmi2"),
            has_bmi1: std::is_x86_feature_detected!("bmi1"),
            has_lzcnt: std::is_x86_feature_detected!("lzcnt"),
            _padding_flags: [0; 4],
        }
    }

    /// The number of elements currently stored in the glass structure.
    pub fn glass_size(&self) -> usize {
        self.arena[self.root].count as usize
    }

    #[inline(always)]
    pub fn insert(&mut self, key: u32, value: u64) {
        if value == 0 {
            self.remove(key);
            return;
        }
        if self.get(key).is_some() {
            self.update_value(key, |v| *v = value);
        } else if self.check_bounds_and_thres(key) {
            if self.glass_size() < MAX_SIZE {
                self.glass_insert(key, value);
            } else {
                if let Some((worst_key, worst_v)) = self.glass_max() {
                    self.glass_remove(worst_key);
                    unsafe {
                        let preempt = &mut *self.preempt.get();
                        preempt.insert(worst_key, worst_v);
                    }
                    self.preempt_bounds_valid.set(false);
                }
                self.glass_insert(key, value);
            }
        } else {
            unsafe {
                let preempt = &mut *self.preempt.get();
                preempt.insert(key, value);
            }
            self.preempt_bounds_valid.set(false);
        }
    }

    #[inline(always)]
    pub fn get(&self, key: u32) -> Option<u64> {
        if self.check_bounds_and_thres(key) {
            self.glass_get(key)
        } else {
            unsafe { (*self.preempt.get()).get(&key).copied() }
        }
    }

    /// Removes and returns the k-th smallest element from the entire collection (glass + preempt).
    ///
    /// The overall sorted order is all glass elements followed by all preempt elements.
    /// Complexity is dominated by sorting the preempt map's keys if the index `k`
    /// falls within the preempt map's range.
    ///
    /// # Arguments
    /// * `k`: The 0-based index of the element to remove.
    ///
    /// # Returns
    /// `Some((key, value))` of the removed element, or `None` if `k` is out of bounds.
    #[inline(always)]
    pub fn remove_by_index(&mut self, k: usize) -> Option<(u32, u64)> {
        let glass_size = self.glass_size();

        let key_to_remove = if k < glass_size {
            // The k-th element is in the glass. Find its key.
            self.glass_find_kth_key(k)?
        } else {
            // The k-th element is in the preempt map.
            let preempt_k = k - glass_size;
            let preempt_map = unsafe { &*self.preempt.get() };
            if preempt_k >= preempt_map.len() {
                return None; // k is out of bounds.
            }

            // This is O(M log M) where M is preempt size, but unavoidable for a HashMap.
            let mut keys: Vec<u32> = preempt_map.keys().cloned().collect();
            keys.sort_unstable();
            keys[preempt_k]
        };

        // Use the existing general-purpose remove function, which will correctly
        // handle state changes (including glass counts).
        self.remove(key_to_remove)
            .map(|value| (key_to_remove, value))
    }

    #[inline(always)]
    pub fn update_value(&mut self, key: u32, f: impl FnOnce(&mut u64)) -> bool {
        if self.check_bounds_and_thres(key) {
            if let Some(mut_ref) = self.glass_get_mut(key) {
                f(mut_ref);
                true
            } else {
                false
            }
        } else {
            unsafe {
                if let Some(v) = (*self.preempt.get()).get_mut(&key) {
                    f(v);
                    true
                } else {
                    false
                }
            }
        }
    }

    #[inline(always)]
    pub fn remove(&mut self, key: u32) -> Option<u64> {
        if self.check_bounds_and_thres(key) {
            // glass_remove now handles count updates, so we don't need to manage `size` here.
            self.glass_remove(key)
        } else {
            unsafe {
                let preempt = &mut *self.preempt.get();
                preempt.remove(&key).inspect(|_val| {
                    if preempt.is_empty() {
                        self.thres.set(u32::MAX);
                        self.preempt_min.set(u32::MAX);
                        self.preempt_max.set(0);
                        self.preempt_bounds_valid.set(true);
                    } else {
                        self.preempt_bounds_valid.set(false);
                    }
                })
            }
        }
    }

    #[inline(always)]
    fn check_bounds_and_thres(&self, key: u32) -> bool {
        let thres = self.thres.get();
        if thres == u32::MAX && !self.preempt_bounds_valid.get() {
            self.update_preempt_bounds();
        }
        key < self.thres.get()
    }

    #[inline(always)]
    pub fn min(&self) -> Option<(u32, u64)> {
        if !self.preempt_bounds_valid.get() {
            self.update_preempt_bounds();
        }

        let glass_min = self.glass_min();
        let preempt_min_key = self.preempt_min.get();
        let preempt_has_min = preempt_min_key != u32::MAX;

        match (glass_min, preempt_has_min) {
            (Some((t_key, t_val)), true) => {
                if t_key <= preempt_min_key {
                    Some((t_key, t_val))
                } else {
                    let v = unsafe {
                        *self
                            .preempt
                            .get()
                            .as_ref()
                            .unwrap()
                            .get(&preempt_min_key)
                            .unwrap()
                    };
                    Some((preempt_min_key, v))
                }
            }
            (Some(t), false) => Some(t),
            (None, true) => {
                let v = unsafe {
                    *self
                        .preempt
                        .get()
                        .as_ref()
                        .unwrap()
                        .get(&preempt_min_key)
                        .unwrap()
                };
                Some((preempt_min_key, v))
            }
            (None, false) => None,
        }
    }

    #[inline(always)]
    pub fn max(&self) -> Option<(u32, u64)> {
        if !self.preempt_bounds_valid.get() {
            self.update_preempt_bounds();
        }

        let glass_max = self.glass_max();
        let preempt_max_key = self.preempt_max.get();
        let preempt_has_max = preempt_max_key != 0;

        match (glass_max, preempt_has_max) {
            (Some((t_key, t_val)), true) => {
                if t_key >= preempt_max_key {
                    Some((t_key, t_val))
                } else {
                    let v = unsafe {
                        *self
                            .preempt
                            .get()
                            .as_ref()
                            .unwrap()
                            .get(&preempt_max_key)
                            .unwrap()
                    };
                    Some((preempt_max_key, v))
                }
            }
            (Some(t), false) => Some(t),
            (None, true) => {
                let v = unsafe {
                    *self
                        .preempt
                        .get()
                        .as_ref()
                        .unwrap()
                        .get(&preempt_max_key)
                        .unwrap()
                };
                Some((preempt_max_key, v))
            }
            (None, false) => None,
        }
    }

    #[inline(always)]
    fn update_preempt_bounds(&self) {
        unsafe {
            let preempt = &*self.preempt.get();
            if preempt.is_empty() {
                self.thres.set(u32::MAX);
                self.preempt_min.set(u32::MAX);
                self.preempt_max.set(0);
            } else {
                let new_min = *preempt.keys().min().unwrap_unchecked();
                let new_max = *preempt.keys().max().unwrap_unchecked();
                self.thres.set(new_min);
                self.preempt_min.set(new_min);
                self.preempt_max.set(new_max);
            }
        }
        self.preempt_bounds_valid.set(true);
    }

    #[inline(always)]
    fn restructure(&mut self) {
        let sigma = self.glass_size();
        if sigma >= MAX_SIZE {
            return;
        }
        let n = MAX_SIZE - sigma;

        let mut to_move = vec![];
        unsafe {
            let preempt = &mut *self.preempt.get();
            if preempt.is_empty() {
                return;
            }
            let mut keys_vec: Vec<u32> = preempt.keys().cloned().collect();
            keys_vec.sort_unstable();
            for k in keys_vec.into_iter().take(n) {
                if let Some(v) = preempt.remove(&k) {
                    to_move.push((k, v));
                }
            }
        }
        for (k, v) in to_move {
            self.glass_insert(k, v);
        }
        self.preempt_bounds_valid.set(false);
    }

    #[inline(always)]
    pub fn buy_shares(&mut self, mut shares_to_buy: u64) -> u64 {
        let mut total_cost = 0u64;

        if self.glass_size() == 0 && !unsafe { (&*self.preempt.get()).is_empty() } {
            self.restructure();
        }

        while shares_to_buy > 0 {
            if let Some((price, _)) = self.glass_min() {
                let mut is_empty = false;
                let updated = self.update_value(price, |avail| {
                    let buy = (*avail).min(shares_to_buy);
                    total_cost += (price as u64) * buy;
                    *avail -= buy;
                    shares_to_buy -= buy;
                    is_empty = *avail == 0;
                });

                if updated && is_empty {
                    self.remove(price);
                    if self.glass_size() < MAX_SIZE {
                        self.restructure();
                    }
                } else if !updated {
                    break;
                }
            } else {
                break;
            }
        }
        total_cost
    }

    #[inline(always)]
    pub fn compute_buy_cost(&self, mut target_shares: u64) -> u64 {
        let mut total_cost = 0u64;
        self.glass_compute_buy_cost(&mut target_shares, &mut total_cost);
        if target_shares > 0 {
            let mut keys: Vec<u32> = unsafe { &*self.preempt.get() }.keys().cloned().collect();
            keys.sort_unstable();
            for k in keys {
                if target_shares == 0 {
                    break;
                }
                let avail_shares = *unsafe { &*self.preempt.get() }.get(&k).unwrap();
                let buy = avail_shares.min(target_shares);
                total_cost = total_cost.saturating_add((k as u64).saturating_mul(buy));
                target_shares -= buy;
            }
        }
        total_cost
    }

    #[inline(always)]
    fn glass_insert(&mut self, key: u32, value: u64) {
        let partial = key >> LAST_BITS;
        let mut level = 0usize;
        let mut node_idx = self.root;

        // --- Path caching for traversal speed ---
        if let Some(lk) = self.cached_last_key.get() {
            let xor = key ^ lk;
            let common_bits = xor.leading_zeros() as usize;
            let lambda = common_bits / BITS_PER_LEVEL;
            level = self.cached_d.get().min(lambda);
            if level > 0 {
                node_idx = unsafe { (*self.cached_path.get())[level] };
            }
        }

        // --- Traverse and create nodes ---
        let current_key = key as u64;
        for l in level..NUM_LEVELS {
            let shift = KEY_BITS.saturating_sub((l + 1) * BITS_PER_LEVEL);
            let bits_this_level = BITS_PER_LEVEL.min(KEY_BITS.saturating_sub(l * BITS_PER_LEVEL));
            let child_mask = (1u64 << bits_this_level) - 1;
            let child_slot = ((current_key >> shift) & child_mask) as usize;

            if self.arena[node_idx].children[child_slot].is_none() {
                let new_idx = if let Some(idx) = self.free_list.pop() {
                    self.arena[idx] = GlassNode::new();
                    idx
                } else {
                    let idx = self.arena.len();
                    self.arena.push(GlassNode::new());
                    idx
                };
                self.arena[node_idx].children[child_slot] = Some(new_idx);
                self.arena[node_idx].mask |= 1u64 << child_slot;
            }
            if l == NUM_LEVELS - 1 {
                unsafe {
                    (*self.cache.get()).entry(partial).or_insert(node_idx);
                }
            }
            unsafe {
                (*self.cached_path.get())[l] = node_idx;
            }
            node_idx = self.arena[node_idx].children[child_slot].unwrap();
        }

        // --- Update leaf and counts ---
        self.arena[node_idx].value = Some(value);
        self.arena[node_idx].count = 1; // A leaf with a value has a count of 1.

        // Increment counts of all ancestors on the path.
        for l in 0..NUM_LEVELS {
            let ancestor_idx = unsafe { (*self.cached_path.get())[l] };
            self.arena[ancestor_idx].count += 1;
        }

        // --- Update global state ---
        self.cached_last_key.set(Some(key));
        self.cached_d.set(NUM_LEVELS);

        if key < self.min_key.get() {
            self.min_key.set(key);
            self.min_leaf.set(Some(node_idx));
        }
        if key > self.max_key.get() {
            self.max_key.set(key);
            self.max_leaf.set(Some(node_idx));
        }
    }

    #[inline(always)]
    fn glass_get(&self, key: u32) -> Option<u64> {
        let partial = key >> LAST_BITS;
        let last = (key & (LAST_MASK as u32)) as usize;
        if let Some(preleaf_idx) = unsafe { (*self.cache.get()).get(&partial).copied() }
            && let Some(leaf_idx) = self.arena[preleaf_idx].children[last]
        {
            return self.arena[leaf_idx].value;
        }

        let mut level = 0usize;
        let mut node_idx = self.root;

        if let Some(lk) = self.cached_last_key.get() {
            let xor = key ^ lk;
            let common_bits = xor.leading_zeros() as usize;
            let lambda = common_bits / BITS_PER_LEVEL;
            level = self.cached_d.get().min(lambda);
            if level > 0 {
                node_idx = unsafe { (*self.cached_path.get())[level] };
            }
        }

        let current_key = key as u64;
        for l in level..NUM_LEVELS {
            let shift = KEY_BITS.saturating_sub((l + 1) * BITS_PER_LEVEL);
            let bits_this_level = BITS_PER_LEVEL.min(KEY_BITS.saturating_sub(l * BITS_PER_LEVEL));
            let child_mask = (1u64 << bits_this_level) - 1;
            let child_slot = ((current_key >> shift) & child_mask) as usize;

            if l == NUM_LEVELS - 1 {
                unsafe {
                    (*self.cache.get()).entry(partial).or_insert(node_idx);
                }
            }
            if let Some(child) = self.arena[node_idx].children[child_slot] {
                unsafe { (*self.cached_path.get())[l] = node_idx };
                node_idx = child;
            } else {
                return None;
            }
        }
        let val = self.arena[node_idx].value;
        if val.is_some() {
            self.cached_last_key.set(Some(key));
            self.cached_d.set(NUM_LEVELS);
        }
        val
    }

    #[inline(always)]
    fn glass_get_mut(&mut self, key: u32) -> Option<&mut u64> {
        let partial = key >> LAST_BITS;
        let last = (key & (LAST_MASK as u32)) as usize;
        if let Some(preleaf_idx) = unsafe { (*self.cache.get()).get(&partial).copied() }
            && let Some(leaf_idx) = self.arena[preleaf_idx].children[last]
        {
            return self.arena[leaf_idx].value.as_mut();
        }

        let mut level = 0usize;
        let mut node_idx = self.root;

        if let Some(lk) = self.cached_last_key.get() {
            let xor = key ^ lk;
            let common_bits = xor.leading_zeros() as usize;
            let lambda = common_bits / BITS_PER_LEVEL;
            level = self.cached_d.get().min(lambda);
            if level > 0 {
                node_idx = unsafe { (*self.cached_path.get())[level] };
            }
        }

        let current_key = key as u64;
        for l in level..NUM_LEVELS {
            let shift = KEY_BITS.saturating_sub((l + 1) * BITS_PER_LEVEL);
            let bits_this_level = BITS_PER_LEVEL.min(KEY_BITS.saturating_sub(l * BITS_PER_LEVEL));
            let child_mask = (1u64 << bits_this_level) - 1;
            let child_slot = ((current_key >> shift) & child_mask) as usize;

            if l == NUM_LEVELS - 1 {
                unsafe {
                    (*self.cache.get()).entry(partial).or_insert(node_idx);
                }
            }
            if let Some(child) = self.arena[node_idx].children[child_slot] {
                unsafe { (*self.cached_path.get())[l] = node_idx };
                node_idx = child;
            } else {
                return None;
            }
        }
        if self.arena[node_idx].value.is_some() {
            self.cached_last_key.set(Some(key));
            self.cached_d.set(NUM_LEVELS);
        }
        self.arena[node_idx].value.as_mut()
    }

    #[inline(always)]
    fn glass_remove(&mut self, key: u32) -> Option<u64> {
        let partial = key >> LAST_BITS;
        let mut path: [(usize, usize); NUM_LEVELS] = [(0, 0); NUM_LEVELS];
        let mut path_len = 0;
        let mut node_idx = self.root;
        let current_key = key as u64;

        for l in 0..NUM_LEVELS {
            let shift = KEY_BITS.saturating_sub((l + 1) * BITS_PER_LEVEL);
            let bits_this_level = BITS_PER_LEVEL.min(KEY_BITS.saturating_sub(l * BITS_PER_LEVEL));
            let child_mask = (1u64 << bits_this_level) - 1;
            let child_slot = ((current_key >> shift) & child_mask) as usize;
            if l == NUM_LEVELS - 1 {
                unsafe {
                    (*self.cache.get()).entry(partial).or_insert(node_idx);
                }
            }
            if let Some(child) = self.arena[node_idx].children[child_slot] {
                path[path_len] = (node_idx, child_slot);
                path_len += 1;
                node_idx = child;
            } else {
                return None;
            }
        }

        let removed = self.arena[node_idx].value.take();
        if removed.is_some() {
            // Key existed and was removed. Update counts.
            self.arena[node_idx].count = 0;
            for (parent_idx, _) in path.iter().take(path_len) {
                self.arena[*parent_idx].count -= 1;
            }
        } else {
            return None; // Key not found
        }

        // --- Prune empty branches ---
        let mut current = node_idx;
        let mut pruned_count = 0;
        let is_last_key = self.cached_last_key.get() == Some(key);

        let mut i = path_len;
        while i > 0 {
            i -= 1;
            let (parent, slot) = path[i];
            if self.arena[current].value.is_some() || self.arena[current].mask != 0 {
                break;
            }
            self.arena[parent].children[slot] = None;
            self.arena[parent].mask &= !(1u64 << slot);
            self.free_list.push(current);

            if i == path_len - 1 && self.arena[parent].mask == 0 {
                unsafe {
                    (*self.cache.get()).remove(&partial);
                }
            }
            pruned_count += 1;
            current = parent;
        }

        if is_last_key {
            self.cached_d
                .set(self.cached_d.get().saturating_sub(pruned_count));
        }

        if key == self.min_key.get() {
            self.min_key.set(u32::MAX);
            self.min_leaf.set(None);
        }
        if key == self.max_key.get() {
            self.max_key.set(0);
            self.max_leaf.set(None);
        }
        removed
    }

    /// Finds the key of the k-th smallest element in the glass.
    #[inline(always)]
    fn glass_find_kth_key(&self, mut k: usize) -> Option<u32> {
        if k >= self.glass_size() {
            return None;
        }

        let mut node_idx = self.root;
        let mut key = 0u32;

        'level_loop: for depth in 0..NUM_LEVELS {
            let node = &self.arena[node_idx];
            let mut start_search_idx = 0;
            loop {
                // Find the next child in ascending order
                if let Some(child_slot) = self.find_next_set_bit(node.mask, start_search_idx) {
                    let child_idx = node.children[child_slot].unwrap();
                    let child_count = self.arena[child_idx].count as usize;

                    if k < child_count {
                        // The k-th element is in this child's subtree. Descend.
                        let shift = KEY_BITS.saturating_sub((depth + 1) * BITS_PER_LEVEL);
                        key |= (child_slot as u32) << shift;
                        node_idx = child_idx;
                        continue 'level_loop;
                    } else {
                        // The k-th element is not here. Skip this subtree's elements.
                        k -= child_count;
                    }
                    // Continue searching for the next sibling
                    start_search_idx = child_slot + 1;
                } else {
                    // This should be unreachable if k and counts are consistent.
                    return None;
                }
            }
        }
        Some(key)
    }

    #[inline(always)]
    fn glass_min(&self) -> Option<(u32, u64)> {
        if let Some(leaf_idx) = self.min_leaf.get() {
            if self.min_key.get() != u32::MAX {
                if let Some(v) = self.arena[leaf_idx].value {
                    return Some((self.min_key.get(), v));
                }
            }
        }
        self.glass_find_extreme(true)
    }

    #[inline(always)]
    fn glass_max(&self) -> Option<(u32, u64)> {
        if let Some(leaf_idx) = self.max_leaf.get() {
            if self.max_key.get() != 0 {
                if let Some(v) = self.arena[leaf_idx].value {
                    return Some((self.max_key.get(), v));
                }
            }
        }
        self.glass_find_extreme(false)
    }

    #[inline(always)]
    fn glass_find_extreme(&self, is_min: bool) -> Option<(u32, u64)> {
        if self.arena[self.root].mask == 0 {
            return None;
        }

        let mut node_idx = self.root;
        let mut key = 0u32;
        for depth in 0..NUM_LEVELS {
            let mask = self.arena[node_idx].mask;
            let bits_this_level =
                BITS_PER_LEVEL.min(KEY_BITS.saturating_sub(depth * BITS_PER_LEVEL));
            let idx = if is_min {
                self.find_next_set_bit(mask, 0)?
            } else {
                self.find_prev_set_bit(mask, 1 << bits_this_level)?
            };
            let shift = KEY_BITS.saturating_sub((depth + 1) * BITS_PER_LEVEL);
            key |= (idx as u32) << shift;
            node_idx = self.arena[node_idx].children[idx].unwrap();
        }

        let value = self.arena[node_idx].value;
        if let Some(v) = value {
            if is_min {
                self.min_key.set(key);
                self.min_leaf.set(Some(node_idx));
            } else {
                self.max_key.set(key);
                self.max_leaf.set(Some(node_idx));
            }
            Some((key, v))
        } else {
            None
        }
    }

    #[inline(always)]
    fn glass_compute_buy_cost(&self, target_shares: &mut u64, total_cost: &mut u64) {
        if *target_shares == 0 || self.arena[self.root].mask == 0 {
            return;
        }
        let mut stack: Vec<StackItem> = Vec::with_capacity(NUM_LEVELS * 2);
        stack.push(StackItem {
            node_idx: self.root,
            depth: 0,
            key: 0,
        });

        while let Some(item) = stack.pop() {
            if *target_shares == 0 {
                break;
            }
            if item.depth as usize == NUM_LEVELS {
                if let Some(avail_shares) = self.arena[item.node_idx].value {
                    let buy = avail_shares.min(*target_shares);
                    *total_cost = total_cost.saturating_add((item.key as u64).saturating_mul(buy));
                    *target_shares -= buy;
                }
                continue;
            }

            let mask = self.arena[item.node_idx].mask;
            let bits_this_level =
                BITS_PER_LEVEL.min(KEY_BITS.saturating_sub(item.depth as usize * BITS_PER_LEVEL));
            let mut child_idx_opt = self.find_prev_set_bit(mask, 1 << bits_this_level);
            while let Some(child_idx) = child_idx_opt {
                let shift = KEY_BITS.saturating_sub((item.depth as usize + 1) * BITS_PER_LEVEL);
                let child_key = item.key | ((child_idx as u32) << shift);
                let child_node_idx = self.arena[item.node_idx].children[child_idx].unwrap();
                stack.push(StackItem {
                    node_idx: child_node_idx,
                    depth: item.depth + 1,
                    key: child_key,
                });
                child_idx_opt = self.find_prev_set_bit(mask, child_idx);
            }
        }
    }

    #[inline(always)]
    fn find_next_set_bit(&self, mut mask: u64, start: usize) -> Option<usize> {
        if start >= NUM_CHILDREN {
            return None;
        }
        mask >>= start;
        if mask == 0 {
            return None;
        }
        let pos = if self.has_bmi1 {
            unsafe { _tzcnt_u64(mask) as usize }
        } else {
            mask.trailing_zeros() as usize
        };
        Some(start + pos)
    }

    #[inline(always)]
    fn find_prev_set_bit(&self, mut mask: u64, end: usize) -> Option<usize> {
        if end == 0 {
            return None;
        }
        if self.has_bmi2 {
            unsafe {
                mask = _bzhi_u64(mask, end as u32);
            }
        } else if end < 64 {
            mask &= (1u64 << end) - 1;
        }
        if mask == 0 {
            return None;
        }
        let pos = if self.has_lzcnt {
            unsafe { (63 - _lzcnt_u64(mask)) as usize }
        } else {
            63 - mask.leading_zeros() as usize
        };
        Some(pos)
    }
}

struct StackItem {
    node_idx: usize,
    depth: u32,
    key: u32,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let glass = Glass::new();
        assert_eq!(glass.glass_size(), 0);
        assert_eq!(glass.arena.len(), 1);
        assert_eq!(glass.root, 0);
        assert!(unsafe { &*glass.cache.get() }.is_empty());
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
        // Insert zero value removes
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

        // Current sorted keys: 5, 10, 20, 30
        assert_eq!(glass.glass_size(), 4);
        assert_eq!(glass.min(), Some((5, 50)));

        // Remove the 2nd smallest element (index 1), which is key 10
        assert_eq!(glass.remove_by_index(1), Some((10, 100)));
        assert_eq!(glass.glass_size(), 3);
        assert_eq!(glass.get(10), None);

        // Current sorted keys: 5, 20, 30
        // Remove the smallest (index 0), which is key 5
        assert_eq!(glass.remove_by_index(0), Some((5, 50)));
        assert_eq!(glass.glass_size(), 2);
        assert_eq!(glass.get(5), None);
        assert_eq!(glass.min(), Some((20, 200)));

        // Current sorted keys: 20, 30
        // Remove the largest (index 1), which is key 30
        assert_eq!(glass.remove_by_index(1), Some((30, 300)));
        assert_eq!(glass.glass_size(), 1);
        assert_eq!(glass.get(30), None);
        assert_eq!(glass.max(), Some((20, 200)));

        // Remove last element
        assert_eq!(glass.remove_by_index(0), Some((20, 200)));
        assert_eq!(glass.glass_size(), 0);
        assert!(glass.min().is_none());

        // Try to remove from empty trie
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
        // Fill beyond MAX_SIZE to trigger preempt
        for i in 0..(MAX_SIZE + 10) {
            glass.insert(i as u32, 1);
        }
        assert_eq!(glass.glass_size(), MAX_SIZE);
        assert!(!unsafe { &*glass.preempt.get() }.is_empty());
        // Restructure should move some from preempt to trie
        glass.remove(0); // Make space in the trie
        assert_eq!(glass.glass_size(), MAX_SIZE - 1);
        let preempt_size_before = unsafe { &*glass.preempt.get() }.len();
        glass.restructure(); // Should pull one item from preempt
        assert_eq!(glass.glass_size(), MAX_SIZE);
        let preempt_size_after = unsafe { &*glass.preempt.get() }.len();
        assert_eq!(preempt_size_after, preempt_size_before - 1);
    }

    #[test]
    fn test_buy_shares() {
        let mut glass = Glass::new();
        glass.insert(10, 500);
        glass.insert(20, 600);
        let cost = glass.buy_shares(700);
        assert_eq!(cost, (10 * 500) + (20 * 200));
        assert_eq!(glass.get(10), None); // Removed since 0
        assert_eq!(glass.get(20), Some(400));
    }

    #[test]
    fn test_compute_buy_cost() {
        let mut glass = Glass::new();
        glass.insert(10, 500);
        glass.insert(20, 600);
        glass.insert(30, 700);
        glass.insert(40, 800);
        let cost = glass.compute_buy_cost(1000);
        assert_eq!(cost, (10 * 500) + (20 * 500)); // Partial
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
        let mut target = 700u64;
        let mut cost = 0u64;
        glass.glass_compute_buy_cost(&mut target, &mut cost);
        assert_eq!(cost, (10 * 500) + (20 * 200));
        assert_eq!(target, 0);
    }

    #[test]
    fn test_find_next_set_bit() {
        let glass = Glass::new();
        let mask = 0b0001_0010; // Bits 1 and 4 set
        assert_eq!(glass.find_next_set_bit(mask, 0), Some(1));
        assert_eq!(glass.find_next_set_bit(mask, 2), Some(4));
        assert_eq!(glass.find_next_set_bit(mask, 5), None);
    }

    #[test]
    fn test_find_prev_set_bit() {
        let glass = Glass::new();
        let mask = 0b0001_0010; // Bits 1 and 4 set
        assert_eq!(glass.find_prev_set_bit(mask, 64), Some(4));
        assert_eq!(glass.find_prev_set_bit(mask, 4), Some(1));
        assert_eq!(glass.find_prev_set_bit(mask, 1), None);
    }
}
