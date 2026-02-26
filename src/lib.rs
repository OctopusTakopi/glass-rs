use ahash::AHashMap as HashMap;
use std::arch::x86_64::*;
use std::cell::{Cell, UnsafeCell};

const BITS_PER_LEVEL: usize = 6;
const NUM_CHILDREN: usize = 1 << BITS_PER_LEVEL;
const PAD_BITS: usize = 4; // 36 total bits -> 6 levels
const NUM_LEVELS: usize = 6;
const MAX_SIZE: usize = 4096;
const HT_SIZE: usize = 4096;
const ARENA_CAPACITY: usize = 16384;
const LEAF_ARENA_CAPACITY: usize = 4096;
const HT_MAX_LOOKUP_LEN: usize = 5;

struct InternalNode {
    mask: u64,
    count: u32,
    parent: u32,
    children: [u32; NUM_CHILDREN],
}

impl InternalNode {
    fn new() -> Self {
        Self {
            mask: 0,
            count: 0,
            parent: u32::MAX,
            children: [u32::MAX; NUM_CHILDREN],
        }
    }
}

struct LeafNode {
    mask: u64,
    ht_next: u32,
    ht_prev: u32,
    ht_k: u32, // partial key (key >> 6)
    next_leaf: u32,
    prev_leaf: u32,
    parent: u32,
    values: [u64; NUM_CHILDREN],
}

impl LeafNode {
    fn new() -> Self {
        Self {
            mask: 0,
            ht_next: u32::MAX,
            ht_prev: u32::MAX,
            ht_k: u32::MAX,
            next_leaf: u32::MAX,
            prev_leaf: u32::MAX,
            parent: u32::MAX,
            values: [0; NUM_CHILDREN],
        }
    }
}

pub struct Glass {
    // === Hot frequently accessed fields ===
    root: u32,
    cached_d: Cell<u32>,
    cached_last_key: Cell<Option<u32>>,
    min_key: Cell<u32>,
    max_key: Cell<u32>,
    preempt_min: Cell<u32>,
    preempt_max: Cell<u32>,
    thres: Cell<u32>,
    min_leaf: Cell<u32>,
    max_leaf: Cell<u32>,

    // Flags
    preempt_bounds_valid: Cell<bool>,
    preempt_dirty: Cell<bool>,
    has_bmi2: bool,
    has_bmi1: bool,
    has_lzcnt: bool,
    _padding_flags: [u8; 3],

    // === Data structures ===
    ht_heads: UnsafeCell<Vec<u32>>,
    preempt: UnsafeCell<HashMap<u32, u64>>,
    cached_path: UnsafeCell<[u32; 5]>, // Levels 0, 1, 2, 3, 4
    cached_leaf: Cell<u32>,
    sorted_preempt_keys: UnsafeCell<Vec<u32>>,

    arena: Vec<InternalNode>,
    free_list: Vec<u32>,

    leaf_arena: Vec<LeafNode>,
    leaf_free_list: Vec<u32>,
}

impl Default for Glass {
    fn default() -> Self {
        Self::new()
    }
}

impl Glass {
    pub fn new() -> Self {
        let mut arena = Vec::with_capacity(ARENA_CAPACITY);
        arena.push(InternalNode::new());
        let ht_heads = vec![u32::MAX; HT_SIZE];

        Glass {
            root: 0,
            cached_d: Cell::new(0),
            cached_last_key: Cell::new(None),
            min_key: Cell::new(u32::MAX),
            max_key: Cell::new(0),
            preempt_min: Cell::new(u32::MAX),
            preempt_max: Cell::new(0),
            thres: Cell::new(u32::MAX),
            min_leaf: Cell::new(u32::MAX),
            max_leaf: Cell::new(u32::MAX),
            preempt_bounds_valid: Cell::new(true),
            preempt_dirty: Cell::new(false),
            has_bmi2: std::is_x86_feature_detected!("bmi2"),
            has_bmi1: std::is_x86_feature_detected!("bmi1"),
            has_lzcnt: std::is_x86_feature_detected!("lzcnt"),
            ht_heads: UnsafeCell::new(ht_heads),
            preempt: UnsafeCell::new(HashMap::new()),
            cached_path: UnsafeCell::new([0; 5]),
            cached_leaf: Cell::new(u32::MAX),
            sorted_preempt_keys: UnsafeCell::new(Vec::new()),
            arena,
            free_list: Vec::new(),
            leaf_arena: Vec::with_capacity(LEAF_ARENA_CAPACITY),
            leaf_free_list: Vec::new(),
            _padding_flags: [0; 3],
        }
    }

    pub fn glass_size(&self) -> usize {
        self.arena[self.root as usize].count as usize
    }

    #[inline(always)]
    fn ensure_sorted_preempt_keys(&self) {
        if self.preempt_dirty.get() {
            unsafe {
                let preempt = &*self.preempt.get();
                let keys = &mut *self.sorted_preempt_keys.get();
                *keys = preempt.keys().cloned().collect();
                keys.sort_unstable();
            }
            self.preempt_dirty.set(false);
        }
    }

    #[inline(always)]
    fn ht_lookup(&self, partial_key: u32) -> Option<u32> {
        let h = (partial_key as usize) & (HT_SIZE - 1);
        let heads = unsafe { &*self.ht_heads.get() };
        let mut curr = heads[h];
        let mut lookups = 0;
        while curr != u32::MAX && lookups < HT_MAX_LOOKUP_LEN {
            let leaf = &self.leaf_arena[curr as usize];
            if leaf.ht_k == partial_key {
                return Some(curr);
            }
            curr = leaf.ht_next;
            lookups += 1;
        }
        None
    }

    #[inline(always)]
    fn ht_insert(&mut self, leaf_idx: u32, partial_key: u32) {
        let h = (partial_key as usize) & (HT_SIZE - 1);
        let heads = unsafe { &mut *self.ht_heads.get() };
        let old_head = heads[h];

        let leaf = &mut self.leaf_arena[leaf_idx as usize];
        leaf.ht_k = partial_key;
        leaf.ht_next = old_head;
        leaf.ht_prev = u32::MAX;

        if old_head != u32::MAX {
            self.leaf_arena[old_head as usize].ht_prev = leaf_idx;
        }
        heads[h] = leaf_idx;
    }

    #[inline(always)]
    fn ht_remove(&mut self, leaf_idx: u32) {
        let leaf = &mut self.leaf_arena[leaf_idx as usize];
        let prev = leaf.ht_prev;
        let next = leaf.ht_next;
        let partial_key = leaf.ht_k;
        
        leaf.ht_k = u32::MAX;
        leaf.ht_next = u32::MAX;
        leaf.ht_prev = u32::MAX;

        if prev != u32::MAX {
            self.leaf_arena[prev as usize].ht_next = next;
        } else {
            let h = (partial_key as usize) & (HT_SIZE - 1);
            unsafe { (&mut *self.ht_heads.get())[h] = next };
        }

        if next != u32::MAX {
            self.leaf_arena[next as usize].ht_prev = prev;
        }
    }

    #[inline(always)]
    pub fn insert(&mut self, key: u32, value: u64) {
        if value == 0 {
            self.remove(key);
            return;
        }
        if self.update_value(key, |v| *v = value) {
            return;
        }

        if self.check_bounds_and_thres(key) {
            if self.glass_size() < MAX_SIZE {
                self.glass_insert(key, value);
            } else {
                if let Some((worst_key, worst_v)) = self.glass_max() {
                    if key < worst_key {
                        self.glass_remove(worst_key);
                        unsafe {
                            let preempt = &mut *self.preempt.get();
                            preempt.insert(worst_key, worst_v);
                        }
                        self.preempt_bounds_valid.set(false);
                        self.preempt_dirty.set(true);
                        self.glass_insert(key, value);
                    } else {
                        unsafe {
                            let preempt = &mut *self.preempt.get();
                            preempt.insert(key, value);
                        }
                        self.preempt_bounds_valid.set(false);
                        self.preempt_dirty.set(true);
                    }
                } else {
                    self.glass_insert(key, value);
                }
            }
        } else {
            unsafe {
                let preempt = &mut *self.preempt.get();
                preempt.insert(key, value);
            }
            self.preempt_bounds_valid.set(false);
            self.preempt_dirty.set(true);
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

    #[inline(always)]
    pub fn remove_by_index(&mut self, k: usize) -> Option<(u32, u64)> {
        if k == 0 {
            return self.min().and_then(|(key, _)| self.remove(key).map(|v| (key, v)));
        }
        
        let glass_size = self.glass_size();

        let key_to_remove = if k < glass_size {
            self.glass_find_kth_key(k)?
        } else {
            let preempt_k = k - glass_size;
            self.ensure_sorted_preempt_keys();
            let keys = unsafe { &*self.sorted_preempt_keys.get() };
            if preempt_k >= keys.len() {
                return None;
            }
            keys[preempt_k]
        };

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
            let res = self.glass_remove(key);
            if res.is_some() && self.glass_size() < MAX_SIZE {
                self.restructure();
            }
            res
        } else {
            unsafe {
                let preempt = &mut *self.preempt.get();
                preempt.remove(&key).inspect(|_val| {
                    if preempt.is_empty() {
                        self.thres.set(u32::MAX);
                        self.preempt_min.set(u32::MAX);
                        self.preempt_max.set(0);
                        self.preempt_bounds_valid.set(true);
                        self.preempt_dirty.set(false);
                    } else {
                        self.preempt_bounds_valid.set(false);
                        self.preempt_dirty.set(true);
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
                let mut new_min = u32::MAX;
                let mut new_max = 0;
                for &k in preempt.keys() {
                    if k < new_min {
                        new_min = k;
                    }
                    if k > new_max {
                        new_max = k;
                    }
                }
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

        self.ensure_sorted_preempt_keys();
        let mut to_move = vec![];
        unsafe {
            let preempt = &mut *self.preempt.get();
            let keys = &*self.sorted_preempt_keys.get();
            for &k in keys.iter().take(n) {
                if let Some(v) = preempt.remove(&k) {
                    to_move.push((k, v));
                }
            }
        }
        for (k, v) in to_move {
            self.glass_insert(k, v);
        }
        self.preempt_bounds_valid.set(false);
        self.preempt_dirty.set(true);
    }

    #[inline(always)]
    pub fn buy_shares(&mut self, mut shares_to_buy: u64) -> u64 {
        let mut total_cost = 0u64;

        if self.glass_size() == 0 && !unsafe { (&*self.preempt.get()).is_empty() } {
            self.restructure();
        }

        while shares_to_buy > 0 {
            if let Some((price, avail_at_price)) = self.min() {
                if avail_at_price <= shares_to_buy {
                    total_cost += (price as u64) * avail_at_price;
                    shares_to_buy -= avail_at_price;
                    self.remove(price);
                } else {
                    total_cost += (price as u64) * shares_to_buy;
                    self.update_value(price, |avail| *avail -= shares_to_buy);
                    shares_to_buy = 0;
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
        
        let mut curr_leaf_idx = self.min_leaf.get();
        while curr_leaf_idx != u32::MAX && target_shares > 0 {
            let leaf = &self.leaf_arena[curr_leaf_idx as usize];
            let base_key = leaf.ht_k << BITS_PER_LEVEL;
            let mut mask = leaf.mask;
            
            // For the very first leaf, we might need to skip some bits
            if base_key == (self.min_key.get() & !0x3F) {
                let start_slot = (self.min_key.get() & 0x3F) as usize;
                mask &= !((1u64 << start_slot) - 1);
            }

            while mask != 0 {
                let slot = if self.has_bmi1 {
                    unsafe { _tzcnt_u64(mask) as usize }
                } else {
                    mask.trailing_zeros() as usize
                };
                
                let price = base_key | (slot as u32);
                let qty = leaf.values[slot];
                let buy = qty.min(target_shares);
                total_cost = total_cost.saturating_add((price as u64).saturating_mul(buy));
                target_shares -= buy;
                
                if target_shares == 0 { return total_cost; }
                
                if self.has_bmi1 {
                    unsafe { mask = _blsr_u64(mask); }
                } else {
                    mask &= !(1u64 << slot);
                }
            }
            curr_leaf_idx = leaf.next_leaf;
        }
        
        if target_shares > 0 {
            self.ensure_sorted_preempt_keys();
            let sorted_keys = unsafe { &*self.sorted_preempt_keys.get() };
            for &k in sorted_keys {
                if target_shares == 0 {
                    break;
                }
                let avail_shares = *unsafe { (*self.preempt.get()).get(&k).unwrap() };
                let buy = avail_shares.min(target_shares);
                total_cost = total_cost.saturating_add((k as u64).saturating_mul(buy));
                target_shares -= buy;
            }
        }
        total_cost
    }

    #[inline(always)]
    fn get_common_prefix_depth(&self, key: u32, lk: u32) -> usize {
        let xor = key ^ lk;
        let lz = xor.leading_zeros() as usize;
        let virtual_lz = lz + PAD_BITS;
        virtual_lz / BITS_PER_LEVEL
    }

    #[inline(always)]
    fn glass_insert(&mut self, key: u32, value: u64) {
        let partial = key >> BITS_PER_LEVEL;
        
        let mut level = 0usize;
        let mut node_idx = self.root;
        let mut leaf_idx = u32::MAX;

        if let Some(l_idx) = self.ht_lookup(partial) {
            leaf_idx = l_idx;
        }

        if leaf_idx != u32::MAX {
            if let Some(lk) = self.cached_last_key.get() {
                let depth = self.get_common_prefix_depth(key, lk);
                level = (self.cached_d.get() as usize).min(depth);
                if level > 0 {
                    if level < NUM_LEVELS - 1 {
                        node_idx = unsafe { (*self.cached_path.get())[level] };
                    }
                }
            }
            
            for l in level..NUM_LEVELS - 1 {
                unsafe { (*self.cached_path.get())[l] = node_idx };
                let shift = (NUM_LEVELS - 1 - l) * BITS_PER_LEVEL;
                let child_slot = ((key >> shift) & 0x3F) as usize;
                node_idx = self.arena[node_idx as usize].children[child_slot];
            }
            let leaf = &mut self.leaf_arena[leaf_idx as usize];
            let leaf_slot = (key & 0x3F) as usize;
            if leaf.values[leaf_slot] == 0 {
                leaf.mask |= 1u64 << leaf_slot;
                for l in 0..NUM_LEVELS - 1 {
                    let ancestor_idx = unsafe { (*self.cached_path.get())[l] };
                    self.arena[ancestor_idx as usize].count += 1;
                }
            }
            leaf.values[leaf_slot] = value;
            
            self.cached_last_key.set(Some(key));
            self.cached_d.set(NUM_LEVELS as u32);
            self.cached_leaf.set(leaf_idx);
            
            if key < self.min_key.get() {
                self.min_key.set(key);
                self.min_leaf.set(leaf_idx);
            }
            if key > self.max_key.get() {
                self.max_key.set(key);
                self.max_leaf.set(leaf_idx);
            }
            return;
        }

        if let Some(lk) = self.cached_last_key.get() {
            let depth = self.get_common_prefix_depth(key, lk);
            level = (self.cached_d.get() as usize).min(depth);
            if level > 0 {
                if level < NUM_LEVELS - 1 {
                    node_idx = unsafe { (*self.cached_path.get())[level] };
                } else {
                    leaf_idx = self.cached_leaf.get();
                }
            }
        }

        for l in level..NUM_LEVELS - 1 {
            let shift = (NUM_LEVELS - 1 - l) * BITS_PER_LEVEL;
            let child_slot = ((key >> shift) & 0x3F) as usize;

            if l == NUM_LEVELS - 2 { 
                if self.arena[node_idx as usize].children[child_slot] == u32::MAX {
                    let new_leaf_idx = if let Some(idx) = self.leaf_free_list.pop() {
                        self.leaf_arena[idx as usize] = LeafNode::new();
                        idx
                    } else {
                        let idx = self.leaf_arena.len() as u32;
                        self.leaf_arena.push(LeafNode::new());
                        idx
                    };
                    
                    self.arena[node_idx as usize].children[child_slot] = new_leaf_idx;
                    self.arena[node_idx as usize].mask |= 1u64 << child_slot;
                    
                    let (prev_l, next_l) = self.find_neighbor_leaves(key);
                    {
                        let new_leaf = &mut self.leaf_arena[new_leaf_idx as usize];
                        new_leaf.parent = node_idx;
                        new_leaf.prev_leaf = prev_l;
                        new_leaf.next_leaf = next_l;
                    }
                    if prev_l != u32::MAX { self.leaf_arena[prev_l as usize].next_leaf = new_leaf_idx; }
                    else { self.min_leaf.set(new_leaf_idx); }
                    if next_l != u32::MAX { self.leaf_arena[next_l as usize].prev_leaf = new_leaf_idx; }
                    else { self.max_leaf.set(new_leaf_idx); }
                    
                    self.ht_insert(new_leaf_idx, partial);
                }
                unsafe { (*self.cached_path.get())[l] = node_idx };
                leaf_idx = self.arena[node_idx as usize].children[child_slot];
            } else { 
                if self.arena[node_idx as usize].children[child_slot] == u32::MAX {
                    let new_idx = if let Some(idx) = self.free_list.pop() {
                        self.arena[idx as usize] = InternalNode::new();
                        idx
                    } else {
                        let idx = self.arena.len() as u32;
                        self.arena.push(InternalNode::new());
                        idx
                    };
                    self.arena[new_idx as usize].parent = node_idx;
                    self.arena[node_idx as usize].children[child_slot] = new_idx;
                    self.arena[node_idx as usize].mask |= 1u64 << child_slot;
                }
                unsafe { (*self.cached_path.get())[l] = node_idx };
                node_idx = self.arena[node_idx as usize].children[child_slot];
            }
        }

        let leaf = &mut self.leaf_arena[leaf_idx as usize];
        let leaf_slot = (key & 0x3F) as usize;
        
        if leaf.values[leaf_slot] == 0 {
            leaf.mask |= 1u64 << leaf_slot;
            for l in 0..NUM_LEVELS - 1 {
                let ancestor_idx = unsafe { (*self.cached_path.get())[l] };
                self.arena[ancestor_idx as usize].count += 1;
            }
        }
        leaf.values[leaf_slot] = value;

        self.cached_last_key.set(Some(key));
        self.cached_d.set(NUM_LEVELS as u32);
        self.cached_leaf.set(leaf_idx);

        if key < self.min_key.get() { self.min_key.set(key); self.min_leaf.set(leaf_idx); }
        if key > self.max_key.get() { self.max_key.set(key); self.max_leaf.set(leaf_idx); }
    }

    #[inline(always)]
    fn find_neighbor_leaves(&self, key: u32) -> (u32, u32) {
        let mut prev = u32::MAX;
        let mut next = u32::MAX;
        
        let mut node_idx = self.root;
        for depth in 0..NUM_LEVELS - 1 {
            let node = &self.arena[node_idx as usize];
            let shift = (NUM_LEVELS - 1 - depth) * BITS_PER_LEVEL;
            let slot = ((key >> shift) & 0x3F) as usize;
            
            if let Some(p_slot) = self.find_prev_set_bit(node.mask, slot) {
                let mut curr = node.children[p_slot];
                for _d2 in depth+1..NUM_LEVELS - 1 {
                    let n2 = &self.arena[curr as usize];
                    let s2 = self.find_prev_set_bit(n2.mask, NUM_CHILDREN).unwrap();
                    curr = n2.children[s2];
                }
                prev = curr;
            }
            if let Some(n_slot) = self.find_next_set_bit(node.mask, slot + 1) {
                let mut curr = node.children[n_slot];
                for _d2 in depth+1..NUM_LEVELS - 1 {
                    let n2 = &self.arena[curr as usize];
                    let s2 = self.find_next_set_bit(n2.mask, 0).unwrap();
                    curr = n2.children[s2];
                }
                next = curr;
            }
            
            let next_node = node.children[slot];
            if next_node == u32::MAX { break; }
            node_idx = next_node;
        }
        (prev, next)
    }

    #[inline(always)]
    fn glass_get(&self, key: u32) -> Option<u64> {
        let partial = key >> BITS_PER_LEVEL;
        if let Some(leaf_idx) = self.ht_lookup(partial) {
            let v = self.leaf_arena[leaf_idx as usize].values[(key & 0x3F) as usize];
            if v > 0 {
                return Some(v);
            }
        }
        None
    }

    #[inline(always)]
    fn glass_get_mut(&mut self, key: u32) -> Option<&mut u64> {
        let partial = key >> BITS_PER_LEVEL;
        if let Some(leaf_idx) = self.ht_lookup(partial) {
            let v = &mut self.leaf_arena[leaf_idx as usize].values[(key & 0x3F) as usize];
            if *v > 0 {
                return Some(v);
            }
        }
        None
    }

    #[inline(always)]
    fn glass_remove(&mut self, key: u32) -> Option<u64> {
        let partial = key >> BITS_PER_LEVEL;
        let leaf_idx = self.ht_lookup(partial)?;
        let leaf_slot = (key & 0x3F) as usize;
        let removed_val = self.leaf_arena[leaf_idx as usize].values[leaf_slot];
        if removed_val == 0 { return None; }

        let mut node_idx = self.root;
        let mut path: [(u32, usize); NUM_LEVELS - 1] = [(0, 0); NUM_LEVELS - 1];
        for l in 0..NUM_LEVELS - 1 {
            let shift = (NUM_LEVELS - 1 - l) * BITS_PER_LEVEL;
            let child_slot = ((key >> shift) & 0x3F) as usize;
            path[l] = (node_idx, child_slot);
            node_idx = self.arena[node_idx as usize].children[child_slot];
        }

        let leaf = &mut self.leaf_arena[leaf_idx as usize];
        leaf.values[leaf_slot] = 0;
        leaf.mask &= !(1u64 << leaf_slot);
        for (parent_idx, _) in path.iter() { self.arena[*parent_idx as usize].count -= 1; }

        if leaf.mask == 0 {
            let p_l = leaf.prev_leaf;
            let n_l = leaf.next_leaf;
            if p_l != u32::MAX { self.leaf_arena[p_l as usize].next_leaf = n_l; }
            else { self.min_leaf.set(n_l); }
            if n_l != u32::MAX { self.leaf_arena[n_l as usize].prev_leaf = p_l; }
            else { self.max_leaf.set(p_l); }

            self.ht_remove(leaf_idx);
            self.leaf_free_list.push(leaf_idx);
            for l in (0..NUM_LEVELS - 1).rev() {
                let (parent, slot) = path[l];
                self.arena[parent as usize].children[slot] = u32::MAX;
                self.arena[parent as usize].mask &= !(1u64 << slot);
                if self.arena[parent as usize].mask == 0 && l > 0 { self.free_list.push(parent); }
                else { break; }
            }
        }

        if self.cached_last_key.get() == Some(key) { self.cached_last_key.set(None); self.cached_d.set(0); }
        if key == self.min_key.get() {
            if let Some((nk, _)) = self.glass_find_extreme(true) { self.min_key.set(nk); }
            else { self.min_key.set(u32::MAX); self.min_leaf.set(u32::MAX); }
        }
        if key == self.max_key.get() {
            if let Some((nk, _)) = self.glass_find_extreme(false) { self.max_key.set(nk); }
            else { self.max_key.set(0); self.max_leaf.set(u32::MAX); }
        }
        Some(removed_val)
    }

    #[inline(always)]
    fn glass_find_kth_key(&self, mut k: usize) -> Option<u32> {
        if k >= self.glass_size() { return None; }
        let mut node_idx = self.root;
        let mut key = 0u32;
        for depth in 0..NUM_LEVELS - 1 {
            let node = &self.arena[node_idx as usize];
            let mut start = 0;
            loop {
                if let Some(slot) = self.find_next_set_bit(node.mask, start) {
                    let child_idx = node.children[slot];
                    let count = if depth == NUM_LEVELS - 2 { self.leaf_arena[child_idx as usize].mask.count_ones() as usize }
                                else { self.arena[child_idx as usize].count as usize };
                    if k < count {
                        key |= (slot as u32) << ((NUM_LEVELS - 1 - depth) * BITS_PER_LEVEL);
                        node_idx = child_idx;
                        break;
                    } else { k -= count; }
                    start = slot + 1;
                } else { return None; }
            }
        }
        let leaf = &self.leaf_arena[node_idx as usize];
        let mut start = 0;
        loop {
            if let Some(slot) = self.find_next_set_bit(leaf.mask, start) {
                if k == 0 { return Some(key | slot as u32); }
                k -= 1;
                start = slot + 1;
            } else { return None; }
        }
    }

    #[inline(always)]
    fn glass_min(&self) -> Option<(u32, u64)> {
        let leaf_idx = self.min_leaf.get();
        if leaf_idx != u32::MAX {
            let leaf = &self.leaf_arena[leaf_idx as usize];
            let slot = leaf.mask.trailing_zeros() as usize;
            return Some(((leaf.ht_k << BITS_PER_LEVEL) | slot as u32, leaf.values[slot]));
        }
        None
    }

    #[inline(always)]
    fn glass_max(&self) -> Option<(u32, u64)> {
        let leaf_idx = self.max_leaf.get();
        if leaf_idx != u32::MAX {
            let leaf = &self.leaf_arena[leaf_idx as usize];
            let slot = 63 - leaf.mask.leading_zeros() as usize;
            return Some(((leaf.ht_k << BITS_PER_LEVEL) | slot as u32, leaf.values[slot]));
        }
        None
    }

    #[inline(always)]
    fn glass_find_extreme(&self, is_min: bool) -> Option<(u32, u64)> {
        if self.arena[self.root as usize].mask == 0 { return None; }
        let mut node_idx = self.root;
        let mut key = 0u32;
        for depth in 0..NUM_LEVELS - 1 {
            let node = &self.arena[node_idx as usize];
            let idx = if is_min { self.find_next_set_bit(node.mask, 0) }
                      else { self.find_prev_set_bit(node.mask, NUM_CHILDREN) }?;
            unsafe { (*self.cached_path.get())[depth] = node_idx };
            key |= (idx as u32) << ((NUM_LEVELS - 1 - depth) * BITS_PER_LEVEL);
            node_idx = node.children[idx];
        }
        let leaf_idx = node_idx;
        let leaf = &self.leaf_arena[leaf_idx as usize];
        let idx = if is_min { self.find_next_set_bit(leaf.mask, 0) }
                  else { self.find_prev_set_bit(leaf.mask, NUM_CHILDREN) }?;
        let price = key | idx as u32;
        self.cached_leaf.set(leaf_idx);
        self.cached_last_key.set(Some(price));
        self.cached_d.set(NUM_LEVELS as u32);
        if is_min { self.min_key.set(price); self.min_leaf.set(leaf_idx); }
        else { self.max_key.set(price); self.max_leaf.set(leaf_idx); }
        Some((price, leaf.values[idx]))
    }

    #[inline(always)]
    fn find_next_set_bit(&self, mut mask: u64, start: usize) -> Option<usize> {
        if start >= NUM_CHILDREN { return None; }
        mask >>= start;
        if mask == 0 { return None; }
        let pos = if self.has_bmi1 { unsafe { _tzcnt_u64(mask) as usize } }
                  else { mask.trailing_zeros() as usize };
        Some(start + pos)
    }

    #[inline(always)]
    fn find_prev_set_bit(&self, mut mask: u64, end: usize) -> Option<usize> {
        if end == 0 { return None; }
        if self.has_bmi2 { unsafe { mask = _bzhi_u64(mask, end as u32); } }
        else if end < 64 { mask &= (1u64 << end) - 1; }
        if mask == 0 { return None; }
        let pos = if self.has_lzcnt { unsafe { (63 - _lzcnt_u64(mask)) as usize } }
                  else { 63 - mask.leading_zeros() as usize };
        Some(pos)
    }
}

include!("tests.rs");
