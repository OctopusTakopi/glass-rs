//! # glass-rs
//!
//! A trie-based ordered map from `u32` prices to `u64` quantities, optimized
//! for client-side order books, implementing the *glass* data structure from
//! [arXiv:2506.13991](https://arxiv.org/abs/2506.13991) (Viktor Krapivensky).
//!
//! Market data exhibits *sequential locality* (events cluster near the last
//! touched price) and *edge locality* (events cluster near the best price).
//! Glass exploits both with a shallow radix trie (6 bits/level), a cached
//! traversal path, a bounded intrusive hash-table cache, a doubly-linked leaf
//! list, and a preemption tier that keeps only the best 4096 price levels in
//! the trie.
//!
//! ```
//! use glass_rs::Glass;
//!
//! let mut book = Glass::new();
//! book.insert(100, 500); // price -> quantity
//! book.insert(110, 300);
//! book.insert(90, 400);
//!
//! assert_eq!(book.min(), Some((90, 400)));
//! let cost = book.buy_shares(700); // consumes 90x400, then 100x300
//! assert_eq!(cost, 90 * 400 + 100 * 300);
//! assert_eq!(book.len(), 2); // 200 left at 100, all 300 at 110
//! ```
//!
//! # Semantics
//!
//! - A value of `0` means "absent": [`Glass::insert`] with 0 deletes the
//!   level, and an [`Glass::update_value`] that reaches 0 removes the level.
//! - Cost arithmetic ([`Glass::buy_shares`], [`Glass::compute_buy_cost`]) is
//!   saturating.
//! - `Glass` is single-threaded by design: it is `Send` but not `Sync`,
//!   because read operations update internal caches through interior
//!   mutability.
//! - All CPU features (BMI1/BMI2/LZCNT/POPCNT/AVX-512F+DQ) are detected at
//!   runtime; portable fallbacks are used elsewhere, and the crate builds on
//!   any architecture.
#![warn(missing_docs)]

use ahash::AHashMap as HashMap;
#[cfg(target_arch = "x86_64")]
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

// Tri-state answers of the bounded hash-table probe (paper §5.2), encoded as
// sentinels so the hot path stays a plain u32 compare. Arena indices can
// never reach these values (capacity is far below u32::MAX - 1).
const HT_ABSENT: u32 = u32::MAX;
const HT_UNKNOWN: u32 = u32::MAX - 1;

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

#[cfg(target_arch = "x86_64")]
fn detect_features() -> (bool, bool, bool, bool, bool) {
    (
        std::is_x86_feature_detected!("bmi2"),
        std::is_x86_feature_detected!("bmi1"),
        std::is_x86_feature_detected!("lzcnt"),
        std::is_x86_feature_detected!("avx512f") && std::is_x86_feature_detected!("avx512dq"),
        std::is_x86_feature_detected!("popcnt"),
    )
}

#[cfg(not(target_arch = "x86_64"))]
fn detect_features() -> (bool, bool, bool, bool, bool) {
    (false, false, false, false, false)
}

/// A trie-based ordered map from `u32` prices to `u64` quantities, optimized
/// for client-side order books. See the [crate-level documentation](crate)
/// for the design overview and semantics.
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
    #[cfg_attr(not(target_arch = "x86_64"), allow(dead_code))]
    has_bmi2: bool,
    #[cfg_attr(not(target_arch = "x86_64"), allow(dead_code))]
    has_bmi1: bool,
    #[cfg_attr(not(target_arch = "x86_64"), allow(dead_code))]
    has_lzcnt: bool,
    #[cfg_attr(not(target_arch = "x86_64"), allow(dead_code))]
    has_avx512: bool,
    #[cfg_attr(not(target_arch = "x86_64"), allow(dead_code))]
    has_popcnt: bool,
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
    /// Creates an empty glass with pre-allocated arenas.
    pub fn new() -> Self {
        let mut arena = Vec::with_capacity(ARENA_CAPACITY);
        arena.push(InternalNode::new());
        let ht_heads = vec![u32::MAX; HT_SIZE];
        let (has_bmi2, has_bmi1, has_lzcnt, has_avx512, has_popcnt) = detect_features();

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
            has_bmi2,
            has_bmi1,
            has_lzcnt,
            has_avx512,
            has_popcnt,
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

    /// Number of price levels currently held in the trie tier (at most
    /// `MAX_SIZE`, 4096). Excludes levels preempted into the overflow map;
    /// see [`Glass::len`] for the total.
    pub fn glass_size(&self) -> usize {
        self.arena[self.root as usize].count as usize
    }

    /// Total number of live price levels across both tiers.
    pub fn len(&self) -> usize {
        self.glass_size() + unsafe { (*self.preempt.get()).len() }
    }

    /// Returns `true` if the book holds no price levels.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Removes all price levels, retaining allocated capacity.
    pub fn clear(&mut self) {
        self.arena.clear();
        self.arena.push(InternalNode::new());
        self.free_list.clear();
        self.leaf_arena.clear();
        self.leaf_free_list.clear();
        unsafe {
            (*self.ht_heads.get()).fill(u32::MAX);
            (*self.preempt.get()).clear();
            (*self.sorted_preempt_keys.get()).clear();
        }
        self.cached_d.set(0);
        self.cached_last_key.set(None);
        self.cached_leaf.set(u32::MAX);
        self.min_key.set(u32::MAX);
        self.max_key.set(0);
        self.preempt_min.set(u32::MAX);
        self.preempt_max.set(0);
        self.thres.set(u32::MAX);
        self.min_leaf.set(u32::MAX);
        self.max_leaf.set(u32::MAX);
        self.preempt_bounds_valid.set(true);
        self.preempt_dirty.set(false);
    }

    /// Iterates all `(price, quantity)` levels in ascending price order.
    ///
    /// Walks the linked leaf list (O(1) per level) and then the sorted
    /// overflow tier. The iterator borrows the glass immutably; levels cannot
    /// change while it is alive.
    pub fn iter(&self) -> Iter<'_> {
        self.ensure_sorted_preempt_keys();
        let leaf_idx = self.min_leaf.get();
        let mask = if leaf_idx != u32::MAX {
            self.leaf_arena[leaf_idx as usize].mask
        } else {
            0
        };
        Iter {
            glass: self,
            leaf_idx,
            mask,
            preempt_pos: 0,
        }
    }

    // Iterator positioned at the first level with price >= start.
    fn iter_at(&self, start: u32) -> Iter<'_> {
        self.ensure_sorted_preempt_keys();

        let (leaf_idx, mask) = if self.glass_size() > 0 && start <= self.max_key.get() {
            if start <= self.min_key.get() {
                let li = self.min_leaf.get();
                (li, self.leaf_arena[li as usize].mask)
            } else {
                let partial = start >> BITS_PER_LEVEL;
                let slot = (start & 0x3F) as usize;
                if let Some(li) = self.find_leaf(partial) {
                    // Keep only bits >= slot in the starting leaf.
                    let m = self.leaf_arena[li as usize].mask & (u64::MAX << slot);
                    if m != 0 {
                        (li, m)
                    } else {
                        let nl = self.leaf_arena[li as usize].next_leaf;
                        if nl != u32::MAX {
                            (nl, self.leaf_arena[nl as usize].mask)
                        } else {
                            (u32::MAX, 0)
                        }
                    }
                } else {
                    let (_, nl) = self.find_neighbor_leaves(start);
                    if nl != u32::MAX {
                        (nl, self.leaf_arena[nl as usize].mask)
                    } else {
                        (u32::MAX, 0)
                    }
                }
            }
        } else {
            (u32::MAX, 0)
        };

        let keys = unsafe { &*self.sorted_preempt_keys.get() };
        let preempt_pos = keys.partition_point(|&k| k < start);

        Iter {
            glass: self,
            leaf_idx,
            mask,
            preempt_pos,
        }
    }

    /// Iterates the levels within `range` in ascending price order, like
    /// [`BTreeMap::range`](std::collections::BTreeMap::range).
    pub fn range<R: std::ops::RangeBounds<u32>>(&self, range: R) -> Range<'_> {
        use std::ops::Bound::*;
        let start = match range.start_bound() {
            Unbounded => 0,
            Included(&a) => a,
            Excluded(&a) => match a.checked_add(1) {
                Some(s) => s,
                None => {
                    return Range {
                        inner: self.iter_at(u32::MAX),
                        end: 0,
                        done: true,
                    };
                }
            },
        };
        let (end, empty) = match range.end_bound() {
            Unbounded => (u32::MAX, false),
            Included(&b) => (b, false),
            Excluded(&b) => {
                if b == 0 {
                    (0, true)
                } else {
                    (b - 1, false)
                }
            }
        };
        let done = empty || start > end;
        Range {
            inner: self.iter_at(if done { u32::MAX } else { start }),
            end,
            done,
        }
    }

    /// Returns the lowest level with price strictly greater than `key`
    /// (the paper's `next` operation). O(1) with the linked leaf list when
    /// the key's leaf exists.
    pub fn next_level(&self, key: u32) -> Option<(u32, u64)> {
        if let Some(r) = self.glass_next(key) {
            return Some(r); // glass keys are the smallest: first hit wins
        }
        let preempt = unsafe { &*self.preempt.get() };
        if preempt.is_empty() {
            return None;
        }
        self.ensure_sorted_preempt_keys();
        let keys = unsafe { &*self.sorted_preempt_keys.get() };
        let pos = keys.partition_point(|&k| k <= key);
        keys.get(pos).map(|&k| (k, *preempt.get(&k).unwrap()))
    }

    /// Returns the highest level with price strictly less than `key`
    /// (the paper's `prev` operation).
    pub fn prev_level(&self, key: u32) -> Option<(u32, u64)> {
        // The overflow tier holds the highest prices: check it first.
        let preempt = unsafe { &*self.preempt.get() };
        if !preempt.is_empty() {
            self.ensure_sorted_preempt_keys();
            let keys = unsafe { &*self.sorted_preempt_keys.get() };
            let pos = keys.partition_point(|&k| k < key);
            if pos > 0 {
                let k = keys[pos - 1];
                return Some((k, *preempt.get(&k).unwrap()));
            }
        }
        self.glass_prev(key)
    }

    fn glass_next(&self, key: u32) -> Option<(u32, u64)> {
        if self.glass_size() == 0 || key >= self.max_key.get() {
            return None;
        }
        if key < self.min_key.get() {
            return self.glass_min();
        }
        let partial = key >> BITS_PER_LEVEL;
        let slot = (key & 0x3F) as usize;
        if let Some(li) = self.find_leaf(partial) {
            let leaf = &self.leaf_arena[li as usize];
            if let Some(s) = self.find_next_set_bit(leaf.mask, slot + 1) {
                return Some(((leaf.ht_k << BITS_PER_LEVEL) | s as u32, leaf.values[s]));
            }
            let nl = leaf.next_leaf;
            if nl != u32::MAX {
                let n = &self.leaf_arena[nl as usize];
                let s = self.tz64(n.mask);
                return Some(((n.ht_k << BITS_PER_LEVEL) | s as u32, n.values[s]));
            }
            None
        } else {
            let (_, nl) = self.find_neighbor_leaves(key);
            if nl != u32::MAX {
                let n = &self.leaf_arena[nl as usize];
                let s = self.tz64(n.mask);
                return Some(((n.ht_k << BITS_PER_LEVEL) | s as u32, n.values[s]));
            }
            None
        }
    }

    fn glass_prev(&self, key: u32) -> Option<(u32, u64)> {
        if self.glass_size() == 0 || key <= self.min_key.get() {
            return None;
        }
        if key > self.max_key.get() {
            return self.glass_max();
        }
        let partial = key >> BITS_PER_LEVEL;
        let slot = (key & 0x3F) as usize;
        if let Some(li) = self.find_leaf(partial) {
            let leaf = &self.leaf_arena[li as usize];
            if let Some(s) = self.find_prev_set_bit(leaf.mask, slot) {
                return Some(((leaf.ht_k << BITS_PER_LEVEL) | s as u32, leaf.values[s]));
            }
            let pl = leaf.prev_leaf;
            if pl != u32::MAX {
                let p = &self.leaf_arena[pl as usize];
                let s = self.high_bit(p.mask);
                return Some(((p.ht_k << BITS_PER_LEVEL) | s as u32, p.values[s]));
            }
            None
        } else {
            let (pl, _) = self.find_neighbor_leaves(key);
            if pl != u32::MAX {
                let p = &self.leaf_arena[pl as usize];
                let s = self.high_bit(p.mask);
                return Some(((p.ht_k << BITS_PER_LEVEL) | s as u32, p.values[s]));
            }
            None
        }
    }

    /// Returns `true` if `key` holds a level.
    pub fn contains_key(&self, key: u32) -> bool {
        self.get(key).is_some()
    }

    /// Returns the `(price, quantity)` pair for `key`, if present.
    pub fn get_key_value(&self, key: u32) -> Option<(u32, u64)> {
        self.get(key).map(|v| (key, v))
    }

    /// Lowest level, like [`BTreeMap::first_key_value`](std::collections::BTreeMap::first_key_value).
    pub fn first_key_value(&self) -> Option<(u32, u64)> {
        self.min()
    }

    /// Highest level, like [`BTreeMap::last_key_value`](std::collections::BTreeMap::last_key_value).
    pub fn last_key_value(&self) -> Option<(u32, u64)> {
        self.max()
    }

    /// Removes and returns the lowest level.
    pub fn pop_first(&mut self) -> Option<(u32, u64)> {
        let (k, _) = self.min()?;
        let v = self.remove(k)?;
        Some((k, v))
    }

    /// Removes and returns the highest level.
    pub fn pop_last(&mut self) -> Option<(u32, u64)> {
        let (k, _) = self.max()?;
        let v = self.remove(k)?;
        Some((k, v))
    }

    /// Iterates prices in ascending order.
    pub fn keys(&self) -> impl Iterator<Item = u32> + '_ {
        self.iter().map(|(k, _)| k)
    }

    /// Iterates quantities in ascending price order.
    pub fn values(&self) -> impl Iterator<Item = u64> + '_ {
        self.iter().map(|(_, v)| v)
    }

    /// Keeps only the levels for which `f` returns `true`.
    pub fn retain(&mut self, mut f: impl FnMut(u32, u64) -> bool) {
        let doomed: Vec<u32> = self
            .iter()
            .filter(|&(k, v)| !f(k, v))
            .map(|(k, _)| k)
            .collect();
        for k in doomed {
            self.remove(k);
        }
    }

    /// Splits the book: `self` keeps levels below `key`, the returned glass
    /// receives levels at or above `key`.
    pub fn split_off(&mut self, key: u32) -> Glass {
        let mut upper = Glass::new();
        let moved: Vec<(u32, u64)> = self.range(key..).collect();
        for (k, v) in moved {
            self.remove(k);
            upper.insert(k, v);
        }
        upper
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

    // Paper §5.2: a bounded chain probe has three possible answers. "Absent"
    // is authoritative (every live leaf is chained), but "Unknown" (chain
    // longer than HT_MAX_LOOKUP_LEN without a match) requires falling back to
    // a full trie descent.
    #[inline(always)]
    fn ht_lookup(&self, partial_key: u32) -> u32 {
        let h = (partial_key as usize) & (HT_SIZE - 1);
        let heads = unsafe { &*self.ht_heads.get() };
        let mut curr = heads[h];
        let mut lookups = 0;
        while curr != u32::MAX && lookups < HT_MAX_LOOKUP_LEN {
            let leaf = &self.leaf_arena[curr as usize];
            if leaf.ht_k == partial_key {
                return curr;
            }
            curr = leaf.ht_next;
            lookups += 1;
        }
        if curr == u32::MAX {
            HT_ABSENT
        } else {
            HT_UNKNOWN
        }
    }

    // Cold fallback for HtAnswer::Unknown — keep it out of line so the hot
    // lookup sites stay small.
    #[cold]
    #[inline(never)]
    fn trie_find_leaf(&self, partial: u32) -> Option<u32> {
        let mut node_idx = self.root;
        for l in 0..NUM_LEVELS - 1 {
            let shift = (NUM_LEVELS - 2 - l) * BITS_PER_LEVEL;
            let slot = ((partial >> shift) & 0x3F) as usize;
            let child = self.arena[node_idx as usize].children[slot];
            if child == u32::MAX {
                return None;
            }
            node_idx = child;
        }
        Some(node_idx)
    }

    #[inline(always)]
    fn find_leaf(&self, partial: u32) -> Option<u32> {
        let r = self.ht_lookup(partial);
        if r < HT_UNKNOWN {
            Some(r)
        } else if r == HT_ABSENT {
            None
        } else {
            self.trie_find_leaf(partial)
        }
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

    // Insert into the preempt tier, maintaining thres/preempt_min/preempt_max
    // eagerly (paper §4.5 assigns the threshold on every preemption). If the
    // bounds are currently invalid they stay invalid and are recomputed lazily.
    #[inline(always)]
    fn preempt_insert(&mut self, key: u32, value: u64) {
        unsafe {
            (*self.preempt.get()).insert(key, value);
        }
        self.preempt_dirty.set(true);
        if self.preempt_bounds_valid.get() {
            if key < self.preempt_min.get() {
                self.preempt_min.set(key);
                self.thres.set(key);
            }
            if key > self.preempt_max.get() {
                self.preempt_max.set(key);
            }
        }
    }

    // Remove from the preempt tier. Bounds stay valid unless a boundary key
    // was removed (then they are recomputed lazily on the next routing check).
    #[inline(always)]
    fn preempt_remove(&mut self, key: u32) -> Option<u64> {
        let preempt = unsafe { &mut *self.preempt.get() };
        let res = preempt.remove(&key);
        if res.is_some() {
            if preempt.is_empty() {
                self.thres.set(u32::MAX);
                self.preempt_min.set(u32::MAX);
                self.preempt_max.set(0);
                self.preempt_bounds_valid.set(true);
                self.preempt_dirty.set(false);
                unsafe { (*self.sorted_preempt_keys.get()).clear() };
            } else {
                self.preempt_dirty.set(true);
                if self.preempt_bounds_valid.get()
                    && (key == self.preempt_min.get() || key == self.preempt_max.get())
                {
                    self.preempt_bounds_valid.set(false);
                }
            }
        }
        res
    }

    /// Inserts or overwrites the quantity at `key`. A `value` of 0 deletes
    /// the level. Amortized O(1) with sequential locality.
    #[inline(always)]
    pub fn insert(&mut self, key: u32, value: u64) {
        if value == 0 {
            self.remove(key);
            return;
        }

        if self.check_bounds_and_thres(key) {
            // Overwrite in place if the key is already present (routing and
            // leaf lookup happen exactly once on this hot path).
            if let Some(v) = self.glass_get_mut(key) {
                *v = value;
                return;
            }
            // New-key creation is kept out of line so the dominant
            // update-in-place path stays a small, layout-stable body.
            self.insert_new_glass_key(key, value);
        } else {
            self.preempt_insert(key, value);
        }
    }

    #[inline(never)]
    fn insert_new_glass_key(&mut self, key: u32, value: u64) {
        if self.glass_size() < MAX_SIZE {
            self.glass_insert(key, value);
        } else if let Some((worst_key, worst_v)) = self.glass_max() {
            if key < worst_key {
                self.glass_remove(worst_key);
                self.preempt_insert(worst_key, worst_v);
                self.glass_insert(key, value);
            } else {
                self.preempt_insert(key, value);
            }
        } else {
            self.glass_insert(key, value);
        }
    }

    /// Returns the quantity at `key`, if present. Hard-bounded O(1) via the
    /// cache table in the common case.
    #[inline(always)]
    pub fn get(&self, key: u32) -> Option<u64> {
        if self.check_bounds_and_thres(key) {
            self.glass_get(key)
        } else {
            unsafe { (*self.preempt.get()).get(&key).copied() }
        }
    }

    /// Removes and returns the `k`-th smallest level (0-indexed), using the
    /// per-subtree counts to descend in O(levels).
    #[inline(always)]
    pub fn remove_by_index(&mut self, k: usize) -> Option<(u32, u64)> {
        if k == 0 {
            return self
                .min()
                .and_then(|(key, _)| self.remove(key).map(|v| (key, v)));
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

    /// Applies `f` to the quantity at `key` in place, returning `true` if the
    /// key was present. If `f` drives the quantity to 0, the level is removed
    /// (the paper's `adjust` semantics — a zero value never stays behind an
    /// occupied slot).
    #[inline(always)]
    pub fn update_value(&mut self, key: u32, f: impl FnOnce(&mut u64)) -> bool {
        if self.check_bounds_and_thres(key) {
            match self.glass_get_mut(key) {
                Some(mut_ref) => {
                    f(mut_ref);
                    if *mut_ref != 0 {
                        return true;
                    }
                    // Restore occupancy so glass_remove can find and unlink
                    // the slot, then remove it properly.
                    *mut_ref = 1;
                }
                None => return false,
            }
            self.remove_zeroed_glass_value(key);
            true
        } else {
            let became_zero = unsafe {
                let preempt = &mut *self.preempt.get();
                match preempt.get_mut(&key) {
                    Some(v) => {
                        f(v);
                        *v == 0
                    }
                    None => return false,
                }
            };
            if became_zero {
                self.preempt_remove(key);
            }
            true
        }
    }

    #[cold]
    #[inline(never)]
    fn remove_zeroed_glass_value(&mut self, key: u32) {
        self.glass_remove(key);
        if self.glass_size() < MAX_SIZE && !unsafe { (*self.preempt.get()).is_empty() } {
            self.restructure();
        }
    }

    /// Removes the level at `key`, returning its quantity if it was present.
    #[inline(always)]
    pub fn remove(&mut self, key: u32) -> Option<u64> {
        if self.check_bounds_and_thres(key) {
            let res = self.glass_remove(key);
            if res.is_some()
                && self.glass_size() < MAX_SIZE
                && !unsafe { (*self.preempt.get()).is_empty() }
            {
                self.restructure();
            }
            res
        } else {
            self.preempt_remove(key)
        }
    }

    #[inline(always)]
    fn check_bounds_and_thres(&self, key: u32) -> bool {
        if !self.preempt_bounds_valid.get() {
            self.update_preempt_bounds();
        }
        key < self.thres.get()
    }

    // Two-tier invariant: every glass key is strictly below thres, and thres
    // is the minimum preempt key. So the global min is the glass min when the
    // glass is non-empty, and the global max is the preempt max when the
    // preempt map is non-empty.
    /// Returns the lowest `(price, quantity)` level, or `None` if empty. O(1).
    #[inline(always)]
    pub fn min(&self) -> Option<(u32, u64)> {
        if let Some(t) = self.glass_min() {
            return Some(t);
        }
        let preempt = unsafe { &*self.preempt.get() };
        if preempt.is_empty() {
            return None;
        }
        if !self.preempt_bounds_valid.get() {
            self.update_preempt_bounds();
        }
        let k = self.preempt_min.get();
        Some((k, *preempt.get(&k).unwrap()))
    }

    /// Returns the highest `(price, quantity)` level, or `None` if empty. O(1)
    /// when the overflow tier is empty or its bounds are cached.
    #[inline(always)]
    pub fn max(&self) -> Option<(u32, u64)> {
        let preempt = unsafe { &*self.preempt.get() };
        if !preempt.is_empty() {
            if !self.preempt_bounds_valid.get() {
                self.update_preempt_bounds();
            }
            let k = self.preempt_max.get();
            return Some((k, *preempt.get(&k).unwrap()));
        }
        self.glass_max()
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
            let keys = &mut *self.sorted_preempt_keys.get();
            let mut take = n.min(keys.len());
            // u32::MAX can never satisfy `key < thres` (thres saturates at
            // u32::MAX, the paper's "infinity"), so it must stay in the
            // preempt tier to remain routable. Sorted, so it can only be last.
            if take > 0 && keys[take - 1] == u32::MAX {
                take -= 1;
            }
            for &k in keys.iter().take(take) {
                if let Some(v) = preempt.remove(&k) {
                    to_move.push((k, v));
                }
            }
            keys.drain(..take);
            // The drained sorted list is exact, so the bounds are too.
            if keys.is_empty() {
                self.thres.set(u32::MAX);
                self.preempt_min.set(u32::MAX);
                self.preempt_max.set(0);
            } else {
                let new_min = keys[0];
                let new_max = *keys.last().unwrap();
                self.thres.set(new_min);
                self.preempt_min.set(new_min);
                self.preempt_max.set(new_max);
            }
        }
        self.preempt_bounds_valid.set(true);
        self.preempt_dirty.set(false);
        for (k, v) in to_move {
            self.glass_insert(k, v);
        }
    }

    // Sum of quantities and slot-weighted quantities of a leaf. Empty slots
    // hold 0, so no mask filtering is needed: the whole-leaf cost is
    // base * sum(qty) + sum(slot * qty).
    #[inline(always)]
    fn leaf_sums(&self, values: &[u64; NUM_CHILDREN]) -> (u64, u64) {
        #[cfg(all(target_arch = "x86_64", not(miri)))]
        if self.has_avx512 {
            return unsafe { leaf_sums_avx512(values) };
        }
        leaf_sums_scalar(values)
    }

    #[inline(always)]
    #[cfg_attr(not(all(target_arch = "x86_64", not(miri))), allow(unused_variables))]
    fn prefetch_leaf(&self, leaf_idx: u32) {
        #[cfg(all(target_arch = "x86_64", not(miri)))]
        if leaf_idx != u32::MAX {
            unsafe {
                _mm_prefetch(
                    std::ptr::from_ref(&self.leaf_arena[leaf_idx as usize]) as *const i8,
                    _MM_HINT_T0,
                );
            }
        }
    }

    // Exclusive-ownership prefetch (prefetchw) for a leaf that is about to be
    // written: the line arrives in Modified/Exclusive state, avoiding the
    // read-then-RFO upgrade that a plain T0 hint would pay.
    #[inline(always)]
    #[cfg_attr(not(all(target_arch = "x86_64", not(miri))), allow(unused_variables))]
    fn prefetch_leaf_w(&self, leaf_idx: u32) {
        #[cfg(all(target_arch = "x86_64", not(miri)))]
        if leaf_idx != u32::MAX {
            unsafe {
                _mm_prefetch(
                    std::ptr::from_ref(&self.leaf_arena[leaf_idx as usize]) as *const i8,
                    _MM_HINT_ET0,
                );
            }
        }
    }

    /// Executes a market buy: consumes `shares_to_buy` from the cheapest
    /// levels upward, deleting depleted levels, and returns the total cost
    /// (saturating). Consumes whole leaves at a time — one vectorized sum +
    /// one ancestor-count walk per 64 price levels.
    pub fn buy_shares(&mut self, mut shares_to_buy: u64) -> u64 {
        let mut total_cost = 0u64;

        while shares_to_buy > 0 {
            if self.glass_size() == 0 {
                if unsafe { (*self.preempt.get()).is_empty() } {
                    break;
                }
                self.restructure();
                if self.glass_size() > 0 {
                    continue;
                }
                // Only the pinned u32::MAX level can be left in the preempt
                // tier (restructure never moves it into the glass).
                let avail = unsafe { (*self.preempt.get()).get(&u32::MAX).copied() };
                let Some(avail) = avail else { break };
                let buy = avail.min(shares_to_buy);
                total_cost = total_cost.saturating_add((u32::MAX as u64).saturating_mul(buy));
                if buy == avail {
                    self.preempt_remove(u32::MAX);
                } else {
                    unsafe {
                        *(*self.preempt.get()).get_mut(&u32::MAX).unwrap() -= buy;
                    }
                }
                break;
            }

            let leaf_idx = self.min_leaf.get();
            let (mask, base, next_leaf) = {
                let leaf = &self.leaf_arena[leaf_idx as usize];
                (
                    leaf.mask,
                    (leaf.ht_k as u64) << BITS_PER_LEVEL,
                    leaf.next_leaf,
                )
            };
            // The successor leaf will be consumed (written) next in a deep
            // sweep — fetch it with intent to write.
            self.prefetch_leaf_w(next_leaf);
            let (qty_total, weighted) = self.leaf_sums(&self.leaf_arena[leaf_idx as usize].values);

            if qty_total <= shares_to_buy {
                // Consume the entire leaf.
                total_cost = total_cost
                    .saturating_add(base.saturating_mul(qty_total))
                    .saturating_add(weighted);
                shares_to_buy -= qty_total;
                self.remove_min_leaf(leaf_idx, mask);
            } else {
                // Partial: walk set bits from the cheapest slot up.
                let leaf = &mut self.leaf_arena[leaf_idx as usize];
                let mut m = mask;
                let mut consumed_slots = 0u32;
                while shares_to_buy > 0 {
                    // plain trailing_zeros: self is mutably borrowed via `leaf`
                    let slot = m.trailing_zeros() as usize;
                    let price = base | slot as u64;
                    let qty = leaf.values[slot];
                    if qty <= shares_to_buy {
                        total_cost = total_cost.saturating_add(price.saturating_mul(qty));
                        shares_to_buy -= qty;
                        leaf.values[slot] = 0;
                        leaf.mask &= !(1u64 << slot);
                        consumed_slots += 1;
                        m &= m - 1;
                    } else {
                        total_cost = total_cost.saturating_add(price.saturating_mul(shares_to_buy));
                        leaf.values[slot] -= shares_to_buy;
                        shares_to_buy = 0;
                    }
                }
                let partial = (base >> BITS_PER_LEVEL) as u32;
                let new_min_slot = self.tz64(self.leaf_arena[leaf_idx as usize].mask) as u32;
                self.min_key.set((base as u32) | new_min_slot);
                if consumed_slots > 0 {
                    self.decrement_ancestor_counts(partial, consumed_slots);
                }
                break;
            }
        }

        if self.glass_size() < MAX_SIZE && !unsafe { (*self.preempt.get()).is_empty() } {
            self.restructure();
        }
        total_cost
    }

    // Unlink and free the current minimum leaf whose (pre-consumption)
    // occupancy mask is `mask`. Ancestor counts, the leaf list, the intrusive
    // hash table, min/max bookkeeping and the cached path are all maintained.
    fn remove_min_leaf(&mut self, leaf_idx: u32, mask: u64) {
        let n = self.popcnt64(mask);
        let (partial, next_l) = {
            let leaf = &mut self.leaf_arena[leaf_idx as usize];
            let p = leaf.ht_k;
            let nl = leaf.next_leaf;
            leaf.mask = 0;
            leaf.values = [0; NUM_CHILDREN];
            (p, nl)
        };

        if next_l != u32::MAX {
            self.leaf_arena[next_l as usize].prev_leaf = u32::MAX;
        } else {
            self.max_leaf.set(u32::MAX);
            self.max_key.set(0);
        }
        self.min_leaf.set(next_l);
        if next_l != u32::MAX {
            let nleaf = &self.leaf_arena[next_l as usize];
            let slot = self.tz64(nleaf.mask) as u32;
            self.min_key.set((nleaf.ht_k << BITS_PER_LEVEL) | slot);
        } else {
            self.min_key.set(u32::MAX);
        }
        self.detach_leaf_from_trie(leaf_idx, partial, n);
    }

    // Mirror of remove_min_leaf for the maximum leaf (sell-side consumption).
    fn remove_max_leaf(&mut self, leaf_idx: u32, mask: u64) {
        let n = self.popcnt64(mask);
        let (partial, prev_l) = {
            let leaf = &mut self.leaf_arena[leaf_idx as usize];
            let p = leaf.ht_k;
            let pl = leaf.prev_leaf;
            leaf.mask = 0;
            leaf.values = [0; NUM_CHILDREN];
            (p, pl)
        };

        if prev_l != u32::MAX {
            self.leaf_arena[prev_l as usize].next_leaf = u32::MAX;
        } else {
            self.min_leaf.set(u32::MAX);
            self.min_key.set(u32::MAX);
        }
        self.max_leaf.set(prev_l);
        if prev_l != u32::MAX {
            let pleaf = &self.leaf_arena[prev_l as usize];
            let slot = self.high_bit(pleaf.mask) as u32;
            self.max_key.set((pleaf.ht_k << BITS_PER_LEVEL) | slot);
        } else {
            self.max_key.set(0);
        }
        self.detach_leaf_from_trie(leaf_idx, partial, n);
    }

    // Shared tail of whole-leaf removal: hash-table unlink, arena free,
    // ancestor count decrements, empty-subtree pruning, and cached-path
    // invalidation. The caller has already emptied the leaf and fixed the
    // leaf list and min/max bookkeeping.
    fn detach_leaf_from_trie(&mut self, leaf_idx: u32, partial: u32, n: u32) {
        self.ht_remove(leaf_idx);
        self.leaf_free_list.push(leaf_idx);

        let mut path: [(u32, usize); NUM_LEVELS - 1] = [(0, 0); NUM_LEVELS - 1];
        let mut node_idx = self.root;
        for (l, entry) in path.iter_mut().enumerate() {
            let shift = (NUM_LEVELS - 2 - l) * BITS_PER_LEVEL;
            let slot = ((partial >> shift) & 0x3F) as usize;
            *entry = (node_idx, slot);
            let next = self.arena[node_idx as usize].children[slot];
            self.arena[node_idx as usize].count -= n;
            node_idx = next;
        }
        debug_assert_eq!(node_idx, leaf_idx);
        for l in (0..NUM_LEVELS - 1).rev() {
            let (parent, slot) = path[l];
            self.arena[parent as usize].children[slot] = u32::MAX;
            self.arena[parent as usize].mask &= !(1u64 << slot);
            if self.arena[parent as usize].mask == 0 && l > 0 {
                self.free_list.push(parent);
            } else {
                break;
            }
        }

        // Cached path entries may point into the freed subtree only when the
        // cached key shared this leaf (shared shallower ancestors survive:
        // their masks are non-zero).
        if let Some(lk) = self.cached_last_key.get()
            && (lk >> BITS_PER_LEVEL) == partial
        {
            self.cached_last_key.set(None);
            self.cached_d.set(0);
        }
    }

    #[inline(always)]
    fn decrement_ancestor_counts(&mut self, partial: u32, n: u32) {
        let mut node_idx = self.root;
        for l in 0..NUM_LEVELS - 1 {
            let shift = (NUM_LEVELS - 2 - l) * BITS_PER_LEVEL;
            let slot = ((partial >> shift) & 0x3F) as usize;
            let node = &mut self.arena[node_idx as usize];
            node.count -= n;
            node_idx = node.children[slot];
        }
    }

    /// Estimates the cost of buying `target_shares` from the cheapest levels
    /// upward without mutating the book (saturating arithmetic). The first
    /// leaf is scanned per-slot so small targets exit immediately; deeper
    /// leaves that are wholly consumed use the vectorized whole-leaf sums.
    pub fn compute_buy_cost(&self, mut target_shares: u64) -> u64 {
        let mut total_cost = 0u64;

        let mut curr_leaf_idx = self.min_leaf.get();
        let mut first = true;
        while curr_leaf_idx != u32::MAX && target_shares > 0 {
            let leaf = &self.leaf_arena[curr_leaf_idx as usize];
            let base = (leaf.ht_k as u64) << BITS_PER_LEVEL;

            if !first {
                // Deep sweep: prefetch the successor while summing this leaf.
                self.prefetch_leaf(leaf.next_leaf);
                let (qty_total, weighted) = self.leaf_sums(&leaf.values);
                if qty_total <= target_shares {
                    total_cost = total_cost
                        .saturating_add(base.saturating_mul(qty_total))
                        .saturating_add(weighted);
                    target_shares -= qty_total;
                    curr_leaf_idx = leaf.next_leaf;
                    continue;
                }
            }
            first = false;

            let mut mask = leaf.mask;
            while mask != 0 {
                let slot = self.tz64(mask);

                let price = base | slot as u64;
                let qty = leaf.values[slot];
                let buy = qty.min(target_shares);
                total_cost = total_cost.saturating_add(price.saturating_mul(buy));
                target_shares -= buy;

                if target_shares == 0 {
                    return total_cost;
                }

                mask = self.clear_lowest_bit(mask);
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

    /// Executes a market sell: consumes `shares_to_sell` from the *highest*
    /// levels downward, deleting depleted levels, and returns the total
    /// proceeds (saturating). The mirror of [`Glass::buy_shares`] — use it
    /// when this glass holds the bid side of a book.
    ///
    /// The overflow tier holds the highest prices, so it is drained first
    /// (sorted, from the top), then trie leaves are consumed whole from the
    /// max leaf backward. Note the preemption design keeps the *lowest* keys
    /// in the fast trie; for a sell-heavy workload against a book deeper than
    /// 4096 levels, consider storing negated prices (`!price`) and using the
    /// buy-side operations instead, so the best bids live in the trie.
    pub fn sell_shares(&mut self, mut shares_to_sell: u64) -> u64 {
        let mut total_proceeds = 0u64;

        // 1. Overflow tier, highest price first.
        if shares_to_sell > 0 && !unsafe { (*self.preempt.get()).is_empty() } {
            self.ensure_sorted_preempt_keys();
            unsafe {
                let preempt = &mut *self.preempt.get();
                let keys = &mut *self.sorted_preempt_keys.get();
                while shares_to_sell > 0 {
                    let Some(&k) = keys.last() else { break };
                    let avail = *preempt.get(&k).unwrap();
                    if avail <= shares_to_sell {
                        total_proceeds =
                            total_proceeds.saturating_add((k as u64).saturating_mul(avail));
                        shares_to_sell -= avail;
                        preempt.remove(&k);
                        keys.pop();
                    } else {
                        total_proceeds = total_proceeds
                            .saturating_add((k as u64).saturating_mul(shares_to_sell));
                        *preempt.get_mut(&k).unwrap() -= shares_to_sell;
                        shares_to_sell = 0;
                    }
                }
                // The drained sorted list stays exact, so set bounds exactly.
                if keys.is_empty() {
                    self.thres.set(u32::MAX);
                    self.preempt_min.set(u32::MAX);
                    self.preempt_max.set(0);
                } else {
                    let new_min = keys[0];
                    self.thres.set(new_min);
                    self.preempt_min.set(new_min);
                    self.preempt_max.set(*keys.last().unwrap());
                }
                self.preempt_bounds_valid.set(true);
            }
        }

        // 2. Glass tier from the max leaf downward.
        while shares_to_sell > 0 && self.glass_size() > 0 {
            let leaf_idx = self.max_leaf.get();
            let (mask, base, prev_leaf) = {
                let leaf = &self.leaf_arena[leaf_idx as usize];
                (
                    leaf.mask,
                    (leaf.ht_k as u64) << BITS_PER_LEVEL,
                    leaf.prev_leaf,
                )
            };
            // The predecessor leaf will be consumed (written) next.
            self.prefetch_leaf_w(prev_leaf);
            let (qty_total, weighted) = self.leaf_sums(&self.leaf_arena[leaf_idx as usize].values);

            if qty_total <= shares_to_sell {
                // Consume the entire leaf.
                total_proceeds = total_proceeds
                    .saturating_add(base.saturating_mul(qty_total))
                    .saturating_add(weighted);
                shares_to_sell -= qty_total;
                self.remove_max_leaf(leaf_idx, mask);
            } else {
                // Partial: walk set bits from the highest slot down.
                let leaf = &mut self.leaf_arena[leaf_idx as usize];
                let mut consumed_slots = 0u32;
                while shares_to_sell > 0 {
                    // plain leading_zeros: self is mutably borrowed via `leaf`
                    let slot = 63 - leaf.mask.leading_zeros() as usize;
                    let price = base | slot as u64;
                    let qty = leaf.values[slot];
                    if qty <= shares_to_sell {
                        total_proceeds = total_proceeds.saturating_add(price.saturating_mul(qty));
                        shares_to_sell -= qty;
                        leaf.values[slot] = 0;
                        leaf.mask &= !(1u64 << slot);
                        consumed_slots += 1;
                    } else {
                        total_proceeds =
                            total_proceeds.saturating_add(price.saturating_mul(shares_to_sell));
                        leaf.values[slot] -= shares_to_sell;
                        shares_to_sell = 0;
                    }
                }
                let partial = (base >> BITS_PER_LEVEL) as u32;
                let new_max_slot = self.high_bit(self.leaf_arena[leaf_idx as usize].mask) as u32;
                self.max_key.set((base as u32) | new_max_slot);
                if consumed_slots > 0 {
                    self.decrement_ancestor_counts(partial, consumed_slots);
                }
                break;
            }
        }
        total_proceeds
    }

    /// Estimates the proceeds of selling `target_shares` into the highest
    /// levels downward without mutating the book (saturating arithmetic).
    /// The mirror of [`Glass::compute_buy_cost`].
    pub fn compute_sell_cost(&self, mut target_shares: u64) -> u64 {
        let mut total_proceeds = 0u64;

        // Overflow tier first: it holds the highest prices.
        {
            let preempt = unsafe { &*self.preempt.get() };
            if !preempt.is_empty() {
                self.ensure_sorted_preempt_keys();
                let keys = unsafe { &*self.sorted_preempt_keys.get() };
                for &k in keys.iter().rev() {
                    if target_shares == 0 {
                        return total_proceeds;
                    }
                    let avail = *preempt.get(&k).unwrap();
                    let take = avail.min(target_shares);
                    total_proceeds = total_proceeds.saturating_add((k as u64).saturating_mul(take));
                    target_shares -= take;
                }
            }
        }

        // Glass tier from the max leaf downward. Same adaptive shape as the
        // buy estimate: first leaf per-slot, deeper leaves vectorized.
        let mut curr_leaf_idx = self.max_leaf.get();
        let mut first = true;
        while curr_leaf_idx != u32::MAX && target_shares > 0 {
            let leaf = &self.leaf_arena[curr_leaf_idx as usize];
            let base = (leaf.ht_k as u64) << BITS_PER_LEVEL;

            if !first {
                self.prefetch_leaf(leaf.prev_leaf);
                let (qty_total, weighted) = self.leaf_sums(&leaf.values);
                if qty_total <= target_shares {
                    total_proceeds = total_proceeds
                        .saturating_add(base.saturating_mul(qty_total))
                        .saturating_add(weighted);
                    target_shares -= qty_total;
                    curr_leaf_idx = leaf.prev_leaf;
                    continue;
                }
            }
            first = false;

            let mut mask = leaf.mask;
            while mask != 0 {
                let slot = self.high_bit(mask);
                let price = base | slot as u64;
                let qty = leaf.values[slot];
                let take = qty.min(target_shares);
                total_proceeds = total_proceeds.saturating_add(price.saturating_mul(take));
                target_shares -= take;
                if target_shares == 0 {
                    return total_proceeds;
                }
                mask &= !(1u64 << slot);
            }
            curr_leaf_idx = leaf.prev_leaf;
        }
        total_proceeds
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

        if let Some(l_idx) = self.find_leaf(partial) {
            leaf_idx = l_idx;
        }

        if leaf_idx != u32::MAX {
            if let Some(lk) = self.cached_last_key.get() {
                let depth = self.get_common_prefix_depth(key, lk);
                level = (self.cached_d.get() as usize).min(depth);
                if level > 0 && level < NUM_LEVELS - 1 {
                    node_idx = unsafe { (*self.cached_path.get())[level] };
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
                    if prev_l != u32::MAX {
                        self.leaf_arena[prev_l as usize].next_leaf = new_leaf_idx;
                    } else {
                        self.min_leaf.set(new_leaf_idx);
                    }
                    if next_l != u32::MAX {
                        self.leaf_arena[next_l as usize].prev_leaf = new_leaf_idx;
                    } else {
                        self.max_leaf.set(new_leaf_idx);
                    }

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

        if key < self.min_key.get() {
            self.min_key.set(key);
            self.min_leaf.set(leaf_idx);
        }
        if key > self.max_key.get() {
            self.max_key.set(key);
            self.max_leaf.set(leaf_idx);
        }
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
                for _d2 in depth + 1..NUM_LEVELS - 1 {
                    let n2 = &self.arena[curr as usize];
                    let s2 = self.find_prev_set_bit(n2.mask, NUM_CHILDREN).unwrap();
                    curr = n2.children[s2];
                }
                prev = curr;
            }
            if let Some(n_slot) = self.find_next_set_bit(node.mask, slot + 1) {
                let mut curr = node.children[n_slot];
                for _d2 in depth + 1..NUM_LEVELS - 1 {
                    let n2 = &self.arena[curr as usize];
                    let s2 = self.find_next_set_bit(n2.mask, 0).unwrap();
                    curr = n2.children[s2];
                }
                next = curr;
            }

            let next_node = node.children[slot];
            if next_node == u32::MAX {
                break;
            }
            node_idx = next_node;
        }
        (prev, next)
    }

    #[inline(always)]
    fn glass_get(&self, key: u32) -> Option<u64> {
        let partial = key >> BITS_PER_LEVEL;
        if let Some(leaf_idx) = self.find_leaf(partial) {
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
        if let Some(leaf_idx) = self.find_leaf(partial) {
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
        let leaf_idx = self.find_leaf(partial)?;
        let leaf_slot = (key & 0x3F) as usize;
        let removed_val = self.leaf_arena[leaf_idx as usize].values[leaf_slot];
        if removed_val == 0 {
            return None;
        }

        let mut node_idx = self.root;
        let mut path: [(u32, usize); NUM_LEVELS - 1] = [(0, 0); NUM_LEVELS - 1];
        for (l, entry) in path.iter_mut().enumerate() {
            let shift = (NUM_LEVELS - 1 - l) * BITS_PER_LEVEL;
            let child_slot = ((key >> shift) & 0x3F) as usize;
            *entry = (node_idx, child_slot);
            node_idx = self.arena[node_idx as usize].children[child_slot];
        }

        let leaf = &mut self.leaf_arena[leaf_idx as usize];
        leaf.values[leaf_slot] = 0;
        leaf.mask &= !(1u64 << leaf_slot);
        for (parent_idx, _) in path.iter() {
            self.arena[*parent_idx as usize].count -= 1;
        }

        if leaf.mask == 0 {
            let p_l = leaf.prev_leaf;
            let n_l = leaf.next_leaf;
            if p_l != u32::MAX {
                self.leaf_arena[p_l as usize].next_leaf = n_l;
            } else {
                self.min_leaf.set(n_l);
            }
            if n_l != u32::MAX {
                self.leaf_arena[n_l as usize].prev_leaf = p_l;
            } else {
                self.max_leaf.set(p_l);
            }

            self.ht_remove(leaf_idx);
            self.leaf_free_list.push(leaf_idx);
            for l in (0..NUM_LEVELS - 1).rev() {
                let (parent, slot) = path[l];
                self.arena[parent as usize].children[slot] = u32::MAX;
                self.arena[parent as usize].mask &= !(1u64 << slot);
                if self.arena[parent as usize].mask == 0 && l > 0 {
                    self.free_list.push(parent);
                } else {
                    break;
                }
            }
        }

        if self.cached_last_key.get() == Some(key) {
            self.cached_last_key.set(None);
            self.cached_d.set(0);
        }
        if key == self.min_key.get() {
            if let Some((nk, _)) = self.glass_find_extreme(true) {
                self.min_key.set(nk);
            } else {
                self.min_key.set(u32::MAX);
                self.min_leaf.set(u32::MAX);
            }
        }
        if key == self.max_key.get() {
            if let Some((nk, _)) = self.glass_find_extreme(false) {
                self.max_key.set(nk);
            } else {
                self.max_key.set(0);
                self.max_leaf.set(u32::MAX);
            }
        }
        Some(removed_val)
    }

    #[inline(always)]
    fn glass_find_kth_key(&self, mut k: usize) -> Option<u32> {
        if k >= self.glass_size() {
            return None;
        }
        let mut node_idx = self.root;
        let mut key = 0u32;
        for depth in 0..NUM_LEVELS - 1 {
            let node = &self.arena[node_idx as usize];
            let mut start = 0;
            loop {
                {
                    let slot = self.find_next_set_bit(node.mask, start)?;
                    let child_idx = node.children[slot];
                    let count = if depth == NUM_LEVELS - 2 {
                        self.popcnt64(self.leaf_arena[child_idx as usize].mask) as usize
                    } else {
                        self.arena[child_idx as usize].count as usize
                    };
                    if k < count {
                        key |= (slot as u32) << ((NUM_LEVELS - 1 - depth) * BITS_PER_LEVEL);
                        node_idx = child_idx;
                        break;
                    } else {
                        k -= count;
                    }
                    start = slot + 1;
                }
            }
        }
        let leaf = &self.leaf_arena[node_idx as usize];
        // The descent guarantees k < popcount(leaf.mask).
        Some(key | self.select_kth_set_bit(leaf.mask, k as u32) as u32)
    }

    // Index of the k-th (0-based) set bit of `mask`; requires
    // k < popcount(mask). PDEP deposits a unit bit into the k-th set
    // position, turning an up-to-64-iteration scan into two instructions.
    // Runtime-gated on BMI2: PDEP is 3 cycles on Intel and Zen 3+, but
    // microcoded (hundreds of cycles) on older AMD, where the fallback loop
    // is preferable anyway.
    #[inline(always)]
    fn select_kth_set_bit(&self, mask: u64, k: u32) -> usize {
        #[cfg(target_arch = "x86_64")]
        if self.has_bmi2 {
            return unsafe { _tzcnt_u64(_pdep_u64(1u64 << k, mask)) as usize };
        }
        let mut m = mask;
        for _ in 0..k {
            m &= m.wrapping_sub(1);
        }
        m.trailing_zeros() as usize
    }

    #[inline(always)]
    fn glass_min(&self) -> Option<(u32, u64)> {
        let leaf_idx = self.min_leaf.get();
        if leaf_idx != u32::MAX {
            let leaf = &self.leaf_arena[leaf_idx as usize];
            let slot = self.tz64(leaf.mask);
            return Some((
                (leaf.ht_k << BITS_PER_LEVEL) | slot as u32,
                leaf.values[slot],
            ));
        }
        None
    }

    #[inline(always)]
    fn glass_max(&self) -> Option<(u32, u64)> {
        let leaf_idx = self.max_leaf.get();
        if leaf_idx != u32::MAX {
            let leaf = &self.leaf_arena[leaf_idx as usize];
            let slot = self.high_bit(leaf.mask);
            return Some((
                (leaf.ht_k << BITS_PER_LEVEL) | slot as u32,
                leaf.values[slot],
            ));
        }
        None
    }

    #[inline(always)]
    fn glass_find_extreme(&self, is_min: bool) -> Option<(u32, u64)> {
        if self.arena[self.root as usize].mask == 0 {
            return None;
        }
        let mut node_idx = self.root;
        let mut key = 0u32;
        for depth in 0..NUM_LEVELS - 1 {
            let node = &self.arena[node_idx as usize];
            let idx = if is_min {
                self.find_next_set_bit(node.mask, 0)
            } else {
                self.find_prev_set_bit(node.mask, NUM_CHILDREN)
            }?;
            unsafe { (*self.cached_path.get())[depth] = node_idx };
            key |= (idx as u32) << ((NUM_LEVELS - 1 - depth) * BITS_PER_LEVEL);
            node_idx = node.children[idx];
        }
        let leaf_idx = node_idx;
        let leaf = &self.leaf_arena[leaf_idx as usize];
        let idx = if is_min {
            self.find_next_set_bit(leaf.mask, 0)
        } else {
            self.find_prev_set_bit(leaf.mask, NUM_CHILDREN)
        }?;
        let price = key | idx as u32;
        self.cached_leaf.set(leaf_idx);
        self.cached_last_key.set(Some(price));
        self.cached_d.set(NUM_LEVELS as u32);
        if is_min {
            self.min_key.set(price);
            self.min_leaf.set(leaf_idx);
        } else {
            self.max_key.set(price);
            self.max_leaf.set(leaf_idx);
        }
        Some((price, leaf.values[idx]))
    }

    // Index of the lowest set bit; hardware tzcnt when available. `mask`
    // must be non-zero on the BMI1 path callers use.
    #[inline(always)]
    fn tz64(&self, mask: u64) -> usize {
        #[cfg(target_arch = "x86_64")]
        if self.has_bmi1 {
            return unsafe { _tzcnt_u64(mask) as usize };
        }
        mask.trailing_zeros() as usize
    }

    // Clears the lowest set bit (blsr).
    #[inline(always)]
    fn clear_lowest_bit(&self, mask: u64) -> u64 {
        #[cfg(target_arch = "x86_64")]
        if self.has_bmi1 {
            return unsafe { _blsr_u64(mask) };
        }
        mask & mask.wrapping_sub(1)
    }

    // Population count. Without -C target-feature=+popcnt, count_ones()
    // compiles to a software fallback on the baseline x86-64 target, so
    // dispatch to the hardware instruction at runtime like the other scans.
    #[inline(always)]
    fn popcnt64(&self, mask: u64) -> u32 {
        #[cfg(target_arch = "x86_64")]
        if self.has_popcnt {
            return unsafe { _popcnt64(mask as i64) as u32 };
        }
        mask.count_ones()
    }

    // Index of the highest set bit; hardware lzcnt when available. `mask`
    // must be non-zero.
    #[inline(always)]
    fn high_bit(&self, mask: u64) -> usize {
        #[cfg(target_arch = "x86_64")]
        if self.has_lzcnt {
            return unsafe { (63 - _lzcnt_u64(mask)) as usize };
        }
        63 - mask.leading_zeros() as usize
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
        Some(start + self.tz64(mask))
    }

    #[inline(always)]
    fn find_prev_set_bit(&self, mut mask: u64, end: usize) -> Option<usize> {
        if end == 0 {
            return None;
        }
        #[cfg(target_arch = "x86_64")]
        {
            if self.has_bmi2 {
                unsafe { mask = _bzhi_u64(mask, end as u32) };
            } else if end < 64 {
                mask &= (1u64 << end) - 1;
            }
        }
        #[cfg(not(target_arch = "x86_64"))]
        if end < 64 {
            mask &= (1u64 << end) - 1;
        }
        if mask == 0 {
            return None;
        }
        Some(self.high_bit(mask))
    }
}

// (sum(qty), sum(slot * qty)) over all 64 slots; empty slots are 0 and
// contribute nothing. Sums wrap on overflow (unreachable for realistic
// order-book quantities); callers combine results with saturating arithmetic.
#[inline(always)]
fn leaf_sums_scalar(values: &[u64; NUM_CHILDREN]) -> (u64, u64) {
    let mut qty = 0u64;
    let mut weighted = 0u64;
    for (i, &v) in values.iter().enumerate() {
        qty = qty.wrapping_add(v);
        weighted = weighted.wrapping_add((i as u64).wrapping_mul(v));
    }
    (qty, weighted)
}

// 8 x 512-bit lanes; vpmullq needs AVX-512DQ (Skylake-SP/Cascade Lake+).
// A 256-bit AVX-512VL variant was measured 17% slower on deep estimation
// sweeps and no better on the buy path; the 512-bit frequency-license
// concern does not apply to this bursty usage (8 vpmullq per leaf), so zmm
// is the right width here.
#[cfg(all(target_arch = "x86_64", not(miri)))]
#[target_feature(enable = "avx512f,avx512dq")]
fn leaf_sums_avx512(values: &[u64; NUM_CHILDREN]) -> (u64, u64) {
    unsafe {
        let mut qty = _mm512_setzero_si512();
        let mut weighted = _mm512_setzero_si512();
        let mut idx = _mm512_setr_epi64(0, 1, 2, 3, 4, 5, 6, 7);
        let eight = _mm512_set1_epi64(8);
        for chunk in 0..NUM_CHILDREN / 8 {
            let v = _mm512_loadu_si512(values.as_ptr().add(chunk * 8) as *const _);
            qty = _mm512_add_epi64(qty, v);
            weighted = _mm512_add_epi64(weighted, _mm512_mullo_epi64(v, idx));
            idx = _mm512_add_epi64(idx, eight);
        }
        (
            _mm512_reduce_add_epi64(qty) as u64,
            _mm512_reduce_add_epi64(weighted) as u64,
        )
    }
}

/// Ascending iterator over `(price, quantity)` levels; see [`Glass::iter`].
pub struct Iter<'a> {
    glass: &'a Glass,
    leaf_idx: u32,
    mask: u64,
    preempt_pos: usize,
}

impl Iterator for Iter<'_> {
    type Item = (u32, u64);

    fn next(&mut self) -> Option<(u32, u64)> {
        while self.leaf_idx != u32::MAX {
            if self.mask != 0 {
                let slot = self.glass.tz64(self.mask);
                self.mask = self.glass.clear_lowest_bit(self.mask);
                let leaf = &self.glass.leaf_arena[self.leaf_idx as usize];
                return Some((
                    (leaf.ht_k << BITS_PER_LEVEL) | slot as u32,
                    leaf.values[slot],
                ));
            }
            self.leaf_idx = self.glass.leaf_arena[self.leaf_idx as usize].next_leaf;
            if self.leaf_idx != u32::MAX {
                self.mask = self.glass.leaf_arena[self.leaf_idx as usize].mask;
            }
        }
        // Overflow tier, in sorted order (prepared by Glass::iter).
        let keys = unsafe { &*self.glass.sorted_preempt_keys.get() };
        if self.preempt_pos < keys.len() {
            let k = keys[self.preempt_pos];
            self.preempt_pos += 1;
            let v = unsafe { *(*self.glass.preempt.get()).get(&k).unwrap() };
            return Some((k, v));
        }
        None
    }
}

impl<'a> IntoIterator for &'a Glass {
    type Item = (u32, u64);
    type IntoIter = Iter<'a>;

    fn into_iter(self) -> Iter<'a> {
        self.iter()
    }
}

/// Ascending iterator over the levels within a price range; see
/// [`Glass::range`].
pub struct Range<'a> {
    inner: Iter<'a>,
    end: u32, // inclusive upper bound
    done: bool,
}

impl Iterator for Range<'_> {
    type Item = (u32, u64);

    fn next(&mut self) -> Option<(u32, u64)> {
        if self.done {
            return None;
        }
        match self.inner.next() {
            Some((k, v)) if k <= self.end => Some((k, v)),
            _ => {
                self.done = true;
                None
            }
        }
    }
}

/// Owning iterator draining levels in ascending price order.
pub struct IntoIter(Glass);

impl Iterator for IntoIter {
    type Item = (u32, u64);

    fn next(&mut self) -> Option<(u32, u64)> {
        self.0.pop_first()
    }
}

impl IntoIterator for Glass {
    type Item = (u32, u64);
    type IntoIter = IntoIter;

    fn into_iter(self) -> IntoIter {
        IntoIter(self)
    }
}

impl std::fmt::Debug for Glass {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Glass")
            .field("len", &self.len())
            .field("trie_len", &self.glass_size())
            .field("min", &self.min())
            .field("max", &self.max())
            .finish_non_exhaustive()
    }
}

impl FromIterator<(u32, u64)> for Glass {
    fn from_iter<T: IntoIterator<Item = (u32, u64)>>(iter: T) -> Self {
        let mut glass = Glass::new();
        glass.extend(iter);
        glass
    }
}

impl Extend<(u32, u64)> for Glass {
    fn extend<T: IntoIterator<Item = (u32, u64)>>(&mut self, iter: T) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

include!("tests.rs");
