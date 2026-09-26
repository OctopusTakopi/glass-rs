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
//! - Cost arithmetic ([`Glass::buy_shares`], [`Glass::compute_buy_cost`] and
//!   the sell-side mirrors) is exact and saturates at `u64::MAX`.
//! - `Glass` is single-threaded by design: it is `Send` but not `Sync`,
//!   because read operations update internal caches through interior
//!   mutability.
//! - SIMD kernels (AVX-512F+DQ, AVX2) and PDEP select are detected at
//!   runtime, with portable fallbacks; the crate builds on any architecture.
//!   Requires a nightly toolchain.
#![warn(missing_docs)]
#![feature(likely_unlikely, hint_prefetch)]

use ahash::AHashMap as HashMap;
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::*;
use std::cell::Cell;
use std::collections::{BTreeSet, btree_set};
use std::ops::Bound;

const BITS_PER_LEVEL: usize = 6;
const NUM_CHILDREN: usize = 1 << BITS_PER_LEVEL;
const PAD_BITS: usize = 4; // 36 total bits -> 6 levels
const NUM_LEVELS: usize = 6;
const MAX_SIZE: usize = 4096;
// Once the trie is REFILL_BATCH levels short, a mutating call pulls at most
// REFILL_BATCH of the lowest preempt levels back into it. Each move is
// O(log p) via the ordered key index, so one refill is bounded (~8k cycles)
// whatever the book depth or however far the trie was drained: after a big
// sweep, later calls top the trie up 32 levels at a time (meanwhile the best
// levels are served, correctly, from the preempt tier). The band also keeps
// top-of-book churn (remove best / insert new best) from ping-ponging a level
// between the tiers on every event, which refilling after every removal did
// (4x slower churn).
const REFILL_BATCH: usize = 32;
const HT_SIZE: usize = 4096;
const ARENA_CAPACITY: usize = 16384;
const LEAF_ARENA_CAPACITY: usize = 4096;
const HT_MAX_LOOKUP_LEN: usize = 5;
// The root is always arena slot 0 (`new` and `clear` push it first).
const ROOT: u32 = 0;

// Branch-probability hints on the hot routing branches, and portable
// prefetches (x86 prefetcht0/prefetchw, aarch64 prfm) for leaf sweeps.
use core::hint::{Locality, likely, prefetch_read, prefetch_write, unlikely};

// A state the internal invariants rule out has been reached: the book is
// corrupt. Fail loudly, in every
// build, at the point of detection. Carrying on would hand the caller
// plausible-looking wrong prices and costs, which for a trading book is
// worse than stopping.
#[cold]
#[inline(never)]
#[track_caller]
fn invariant_violated(what: &'static str) -> ! {
    panic!("glass-rs internal invariant violated: {what}");
}

// Quantity of a key that the preempt key index says is in the preempt map
// (the index and the map always hold the same key set).
#[inline(always)]
#[track_caller]
fn preempt_qty(preempt: &HashMap<u32, u64>, key: u32) -> u64 {
    match preempt.get(&key) {
        Some(&qty) => qty,
        None => invariant_violated("preempt bookkeeping names a key missing from the map"),
    }
}

// Tri-state answers of the bounded hash-table probe (paper §5.2), encoded as
// sentinels so the hot path stays a plain u32 compare. Arena indices can
// never reach these values (capacity is far below u32::MAX - 1).
const HT_ABSENT: u32 = u32::MAX;
const HT_UNKNOWN: u32 = u32::MAX - 1;

struct InternalNode {
    mask: u64,
    count: u32,
    children: [u32; NUM_CHILDREN],
}

impl InternalNode {
    fn new() -> Self {
        Self {
            mask: 0,
            count: 0,
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
    values: [u64; NUM_CHILDREN],
}

impl LeafNode {
    // The `(price, quantity)` level stored in `slot`.
    #[inline(always)]
    fn level(&self, slot: usize) -> (u32, u64) {
        (
            (self.ht_k << BITS_PER_LEVEL) | slot as u32,
            self.values[slot],
        )
    }

    fn new() -> Self {
        Self {
            mask: 0,
            ht_next: u32::MAX,
            ht_prev: u32::MAX,
            ht_k: u32::MAX,
            next_leaf: u32::MAX,
            prev_leaf: u32::MAX,
            values: [0; NUM_CHILDREN],
        }
    }
}

#[cfg(target_arch = "x86_64")]
fn detect_features() -> Features {
    let popcnt = std::is_x86_feature_detected!("popcnt");
    Features {
        fast_pdep: popcnt
            && std::is_x86_feature_detected!("bmi1")
            && std::is_x86_feature_detected!("bmi2")
            && !pdep_is_microcoded(),
        popcnt,
        avx512: std::is_x86_feature_detected!("avx512f")
            && std::is_x86_feature_detected!("avx512dq"),
        avx2: std::is_x86_feature_detected!("avx2"),
    }
}

// AMD before Zen 3 (family 0x19) and Hygon implement PDEP/PEXT in microcode
// (~18-290 cycles, data-dependent); the portable select loop beats it there.
#[cfg(target_arch = "x86_64")]
fn pdep_is_microcoded() -> bool {
    let id = __cpuid(0);
    let vendor = (id.ebx, id.edx, id.ecx);
    let amd = vendor == (0x6874_7541, 0x6974_6e65, 0x444d_4163); // "AuthenticAMD"
    let hygon = vendor == (0x6f67_7948, 0x6e65_476e, 0x656e_6975); // "HygonGenuine"
    if !(amd || hygon) {
        return false;
    }
    let eax = __cpuid(1).eax;
    let base = (eax >> 8) & 0xF;
    let family = if base == 0xF {
        base + ((eax >> 20) & 0xFF)
    } else {
        base
    };
    hygon || family < 0x19
}

#[cfg(not(target_arch = "x86_64"))]
fn detect_features() -> Features {
    Features {
        fast_pdep: false,
        popcnt: false,
        avx512: false,
        avx2: false,
    }
}

// Runtime-detected CPU capabilities used by the dispatched kernels.
#[cfg_attr(not(target_arch = "x86_64"), allow(dead_code))]
struct Features {
    // BMI1 + BMI2 + POPCNT with a hardware (not microcoded) PDEP.
    fast_pdep: bool,
    popcnt: bool,
    avx512: bool,
    avx2: bool,
}

/// A trie-based ordered map from `u32` prices to `u64` quantities, optimized
/// for client-side order books. See the [crate-level documentation](crate)
/// for the design overview and semantics.
pub struct Glass {
    cached_d: Cell<u32>,
    cached_last_key: Cell<Option<u32>>,
    min_key: Cell<u32>,
    max_key: Cell<u32>,
    min_leaf: Cell<u32>,
    max_leaf: Cell<u32>,
    // Routing threshold (paper §4.5): the lowest preempt key, or u32::MAX (the
    // paper's "infinity") when the preempt tier is empty. Kept exact on every
    // key-set change; every trie key is below it.
    thres: u32,

    // `glass_find_kth_key` kernels: POPCNT + hardware PDEP, or POPCNT only.
    #[cfg_attr(not(target_arch = "x86_64"), allow(dead_code))]
    has_fast_pdep: bool,
    #[cfg_attr(not(target_arch = "x86_64"), allow(dead_code))]
    has_popcnt: bool,
    #[cfg_attr(not(target_arch = "x86_64"), allow(dead_code))]
    has_avx512: bool,
    // AVX2 without AVX-512 (Zen 2/3, Intel client): the scalar leaf sums
    // recompiled for AVX2 measured 23-40% faster on deep sweeps.
    #[cfg_attr(not(target_arch = "x86_64"), allow(dead_code))]
    has_avx2: bool,

    ht_heads: Vec<u32>,
    // The preempt (overflow) tier, as in the paper: a hash table, so the
    // common deep-book event, a quantity change at an existing level, is one
    // O(1) hash write.
    preempt: HashMap<u32, u64>,
    // Ordered index of `preempt`'s key set, touched only when a level
    // appears or disappears (O(log p)). It gives O(log p) min/max, refills
    // and ordered walks with no O(p) scan or sort anywhere.
    preempt_keys: BTreeSet<u32>,
    // Internal node at each trie level 0..=4 on the path to `cached_last_key`.
    cached_path: [Cell<u32>; NUM_LEVELS - 1],
    cached_leaf: Cell<u32>,

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
        let cpu = detect_features();

        Glass {
            cached_d: Cell::new(0),
            cached_last_key: Cell::new(None),
            min_key: Cell::new(u32::MAX),
            max_key: Cell::new(0),
            min_leaf: Cell::new(u32::MAX),
            max_leaf: Cell::new(u32::MAX),
            thres: u32::MAX,
            has_fast_pdep: cpu.fast_pdep,
            has_popcnt: cpu.popcnt,
            has_avx512: cpu.avx512,
            has_avx2: cpu.avx2,
            ht_heads,
            preempt: HashMap::new(),
            preempt_keys: BTreeSet::new(),
            cached_path: Default::default(),
            cached_leaf: Cell::new(u32::MAX),
            arena,
            free_list: Vec::new(),
            leaf_arena: Vec::with_capacity(LEAF_ARENA_CAPACITY),
            leaf_free_list: Vec::new(),
        }
    }

    /// Number of price levels currently held in the trie tier (at most
    /// `MAX_SIZE`, 4096). Excludes levels preempted into the overflow map;
    /// see [`Glass::len`] for the total.
    pub fn glass_size(&self) -> usize {
        self.arena[ROOT as usize].count as usize
    }

    /// Total number of live price levels across both tiers.
    pub fn len(&self) -> usize {
        self.glass_size() + self.preempt.len()
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
        self.ht_heads.fill(u32::MAX);
        self.preempt.clear();
        self.preempt_keys.clear();
        self.thres = u32::MAX;
        self.cached_d.set(0);
        self.cached_last_key.set(None);
        self.cached_leaf.set(u32::MAX);
        self.min_key.set(u32::MAX);
        self.max_key.set(0);
        self.min_leaf.set(u32::MAX);
        self.max_leaf.set(u32::MAX);
    }

    /// Iterates all `(price, quantity)` levels in ascending price order.
    ///
    /// Walks the linked leaf list (O(1) per level) and then the sorted
    /// overflow tier. The iterator borrows the glass immutably; levels cannot
    /// change while it is alive.
    pub fn iter(&self) -> Iter<'_> {
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
            preempt: self.preempt_keys.range(..),
        }
    }

    // Iterator positioned at the first level with price >= start.
    fn iter_at(&self, start: u32) -> Iter<'_> {
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

        Iter {
            glass: self,
            leaf_idx,
            mask,
            preempt: self.preempt_keys.range(start..),
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
        let &k = self
            .preempt_keys
            .range((Bound::Excluded(key), Bound::Unbounded))
            .next()?;
        Some((k, preempt_qty(&self.preempt, k)))
    }

    /// Returns the highest level with price strictly less than `key`
    /// (the paper's `prev` operation).
    pub fn prev_level(&self, key: u32) -> Option<(u32, u64)> {
        // The overflow tier holds the highest prices: check it first.
        if let Some(&k) = self.preempt_keys.range(..key).next_back() {
            return Some((k, preempt_qty(&self.preempt, k)));
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
            if let Some(s) = find_next_set_bit(leaf.mask, slot + 1) {
                return Some(leaf.level(s));
            }
            let nl = leaf.next_leaf;
            if nl != u32::MAX {
                let n = &self.leaf_arena[nl as usize];
                let s = tz64(n.mask);
                return Some(n.level(s));
            }
            None
        } else {
            let (_, nl) = self.find_neighbor_leaves(key);
            if nl != u32::MAX {
                let n = &self.leaf_arena[nl as usize];
                let s = tz64(n.mask);
                return Some(n.level(s));
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
            if let Some(s) = find_prev_set_bit(leaf.mask, slot) {
                return Some(leaf.level(s));
            }
            let pl = leaf.prev_leaf;
            if pl != u32::MAX {
                let p = &self.leaf_arena[pl as usize];
                let s = high_bit(p.mask);
                return Some(p.level(s));
            }
            None
        } else {
            let (pl, _) = self.find_neighbor_leaves(key);
            if pl != u32::MAX {
                let p = &self.leaf_arena[pl as usize];
                let s = high_bit(p.mask);
                return Some(p.level(s));
            }
            None
        }
    }

    /// Copies the best (lowest-price) `n` levels into `out` in ascending
    /// order, clearing it first; returns the number written (fewer than `n`
    /// only if the book has fewer levels).
    ///
    /// Designed for top-of-book snapshots — e.g. computing order-book
    /// imbalance over the best N levels each tick. Reuses `out`'s capacity,
    /// so a caller-held buffer makes the steady state allocation-free.
    ///
    /// Where AVX-512 is available, dense leaves are extracted with masked
    /// compress-stores (`vpcompressq`), using the leaf occupancy bitmap
    /// directly as the lane mask; sparse leaves use a scalar bit-scan.
    pub fn top_levels(&self, n: usize, out: &mut Vec<(u32, u64)>) -> usize {
        out.clear();
        if n == 0 {
            return 0;
        }
        out.reserve(n);

        let mut curr = self.min_leaf.get();
        while curr != u32::MAX && out.len() < n {
            let leaf = &self.leaf_arena[curr as usize];
            self.prefetch_leaf(leaf.next_leaf);
            let base = leaf.ht_k << BITS_PER_LEVEL;

            // Vectorized extraction only when the WHOLE leaf is consumed:
            // vpcompressq extracts all 64 slots regardless, so a partial
            // take (typical small n) is cheaper via the scalar scan.
            #[cfg(all(target_arch = "x86_64", not(miri)))]
            {
                let count = leaf.mask.count_ones() as usize;
                if self.has_avx512 && count >= 16 && n - out.len() >= count {
                    unsafe { extract_leaf_avx512(leaf, base, count, out) };
                    curr = leaf.next_leaf;
                    continue;
                }
            }

            let mut mask = leaf.mask;
            while mask != 0 && out.len() < n {
                let slot = mask.trailing_zeros() as usize;
                out.push((base | slot as u32, leaf.values[slot]));
                mask &= mask - 1;
            }
            curr = leaf.next_leaf;
        }

        // Overflow tier tail (only when n exceeds the trie's levels).
        let rest = n - out.len();
        for &k in self.preempt_keys.iter().take(rest) {
            out.push((k, preempt_qty(&self.preempt, k)));
        }
        out.len()
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

    // Paper §5.2: a bounded chain probe has three possible answers. "Absent"
    // is authoritative (every live leaf is chained), but "Unknown" (chain
    // longer than HT_MAX_LOOKUP_LEN without a match) requires falling back to
    // a full trie descent.
    #[inline(always)]
    fn ht_lookup(&self, partial_key: u32) -> u32 {
        let h = (partial_key as usize) & (HT_SIZE - 1);
        let mut curr = self.ht_heads[h];
        let mut lookups = 0;
        while curr != u32::MAX && lookups < HT_MAX_LOOKUP_LEN {
            // Note: an unchecked index here was measured no faster under the
            // JCC-mitigated build (the check's branch predicts perfectly) —
            // keep the safe indexing.
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

    // Full descent, for when `ht_lookup` answers HT_UNKNOWN. Out of line so
    // the hot lookup sites stay small.
    #[cold]
    #[inline(never)]
    fn trie_find_leaf(&self, partial: u32) -> Option<u32> {
        let mut node_idx = ROOT;
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
        if likely(r < HT_UNKNOWN) {
            Some(r)
        } else if likely(r == HT_ABSENT) {
            // "don't know" (a chain past the probe bound) is ~1e-7 (paper §5.3)
            None
        } else {
            self.trie_find_leaf(partial)
        }
    }

    #[inline(always)]
    fn ht_insert(&mut self, leaf_idx: u32, partial_key: u32) {
        let h = (partial_key as usize) & (HT_SIZE - 1);
        let old_head = self.ht_heads[h];

        let leaf = &mut self.leaf_arena[leaf_idx as usize];
        leaf.ht_k = partial_key;
        leaf.ht_next = old_head;
        leaf.ht_prev = u32::MAX;

        if old_head != u32::MAX {
            self.leaf_arena[old_head as usize].ht_prev = leaf_idx;
        }
        self.ht_heads[h] = leaf_idx;
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
            self.ht_heads[h] = next;
        }

        if next != u32::MAX {
            self.leaf_arena[next as usize].ht_prev = prev;
        }
    }

    // Insert into the preempt tier. A quantity overwrite at an existing level
    // is a single hash write; a new level is added to the key index and may
    // lower `thres` (paper §4.5 assigns the threshold on every preemption).
    // Returns whether `key` is a new level.
    #[inline(always)]
    fn preempt_insert(&mut self, key: u32, value: u64) -> bool {
        let new = self.preempt.insert(key, value).is_none();
        if new {
            // Keep capacity >= 2x the live levels. Under deep-book churn the
            // table fills with tombstones, and hashbrown then either rehashes
            // in place (cheap) or, when more than half full, grows: a ~250 us
            // one-off stall measured mid-session. With this headroom it only
            // ever rehashes in place.
            let len = self.preempt.len();
            if self.preempt.capacity() < 2 * len {
                self.preempt.reserve(len);
            }
            self.preempt_keys.insert(key);
            self.thres = self.thres.min(key);
        }
        new
    }

    // Remove from the preempt tier, keeping the key index and `thres` exact.
    #[inline(always)]
    fn preempt_remove(&mut self, key: u32) -> Option<u64> {
        let res = self.preempt.remove(&key);
        if res.is_some() {
            self.preempt_keys.remove(&key);
            if key == self.thres {
                self.refresh_thres();
            }
        }
        res
    }

    // `thres` = the lowest preempt key, or u32::MAX when the tier is empty.
    #[inline(always)]
    fn refresh_thres(&mut self) {
        self.thres = self.preempt_keys.first().copied().unwrap_or(u32::MAX);
    }

    /// Inserts or overwrites the quantity at `key`. A `value` of 0 deletes
    /// the level. Amortized O(1) with sequential locality.
    #[inline(always)]
    pub fn insert(&mut self, key: u32, value: u64) {
        if unlikely(value == 0) {
            self.remove(key);
            return;
        }

        if self.routes_to_trie(key) {
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
            // A drained trie is topped up by later calls, whichever tier they
            // touch, so it cannot stay short. An overwrite of an existing
            // level changes nothing there, so skip the check.
            if self.preempt_insert(key, value) {
                self.refill_if_low();
            }
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
        if self.routes_to_trie(key) {
            self.glass_get(key)
        } else {
            self.preempt.get(&key).copied()
        }
    }

    /// Removes and returns the `k`-th smallest level (0-indexed). Levels in
    /// the trie (the lowest 4096) are found in O(levels) via per-subtree
    /// counts; deeper levels by an O(k) walk of the overflow tier's key index.
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
            // The key index has no rank: O(k) walk past the trie's levels.
            *self.preempt_keys.iter().nth(k - glass_size)?
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
        if self.routes_to_trie(key) {
            match self.glass_get_mut(key) {
                Some(mut_ref) => {
                    f(mut_ref);
                    if likely(*mut_ref != 0) {
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
            let became_zero = match self.preempt.get_mut(&key) {
                Some(v) => {
                    f(v);
                    *v == 0
                }
                None => return false,
            };
            if became_zero {
                self.preempt_remove(key);
                self.refill_if_low();
            }
            true
        }
    }

    #[cold]
    #[inline(never)]
    fn remove_zeroed_glass_value(&mut self, key: u32) {
        self.glass_remove(key);
        self.refill_if_low();
    }

    /// Removes the level at `key`, returning its quantity if it was present.
    #[inline(always)]
    pub fn remove(&mut self, key: u32) -> Option<u64> {
        if self.routes_to_trie(key) {
            let res = self.glass_remove(key);
            if res.is_some() {
                self.refill_if_low();
            }
            res
        } else {
            let res = self.preempt_remove(key);
            if res.is_some() {
                self.refill_if_low();
            }
            res
        }
    }

    // Tier routing: keys below `thres` live in the trie, the rest in the
    // preempt tier (so u32::MAX, which never satisfies `< thres`, is pinned
    // to the preempt tier).
    #[inline(always)]
    fn routes_to_trie(&self, key: u32) -> bool {
        key < self.thres
    }

    // Two-tier invariant: every trie key is strictly below thres, the lowest
    // preempt key. So the global min is the trie min when the trie is
    // non-empty, and the global max is the preempt max when that is non-empty.
    /// Returns the lowest `(price, quantity)` level, or `None` if empty. O(1)
    /// when the trie is non-empty.
    #[inline(always)]
    pub fn min(&self) -> Option<(u32, u64)> {
        if let Some(t) = self.glass_min() {
            return Some(t);
        }
        let &k = self.preempt_keys.first()?;
        Some((k, preempt_qty(&self.preempt, k)))
    }

    /// Returns the highest `(price, quantity)` level, or `None` if empty.
    #[inline(always)]
    pub fn max(&self) -> Option<(u32, u64)> {
        match self.preempt_keys.last() {
            Some(&k) => Some((k, preempt_qty(&self.preempt, k))),
            None => self.glass_max(),
        }
    }

    // Once the trie is REFILL_BATCH levels short, pull up to REFILL_BATCH of
    // the lowest preempt levels back (paper §4.5). Called at the end of every
    // mutating operation that can leave the trie short. Correctness only
    // needs trie keys < thres, not a full trie.
    #[inline(always)]
    fn refill_if_low(&mut self) {
        if self.glass_size() <= MAX_SIZE - REFILL_BATCH && !self.preempt_keys.is_empty() {
            self.restructure();
        }
    }

    // Moves up to REFILL_BATCH of the lowest preempt levels into the trie (no
    // further than full). u32::MAX can never satisfy `key < thres` (thres
    // saturates at u32::MAX, the paper's "infinity"), so it stays in the
    // preempt tier to remain routable; being the largest key, it is the last
    // one reached.
    #[inline(always)]
    fn restructure(&mut self) {
        let mut room = MAX_SIZE.saturating_sub(self.glass_size()).min(REFILL_BATCH);
        while room > 0 {
            let Some(&k) = self.preempt_keys.first() else {
                break;
            };
            if k == u32::MAX {
                break;
            }
            self.preempt_keys.pop_first();
            let v = match self.preempt.remove(&k) {
                Some(v) => v,
                None => invariant_violated("preempt key index names a key missing from the map"),
            };
            self.glass_insert(k, v);
            room -= 1;
        }
        self.refresh_thres();
    }

    // Exact `(sum(qty), min(sum(slot * qty), u64::MAX))` of a leaf, or `None`
    // when sum(qty) does not fit in u64 (the leaf then holds more than any
    // u64 order can take, so callers fall back to the per-slot walk). Empty
    // slots hold 0, so no mask filtering is needed: the whole-leaf cost is
    // base * sum(qty) + sum(slot * qty). The fast path sums with wrapping
    // arithmetic, which is exact while every quantity is below
    // LEAF_SUM_EXACT_BOUND; the rare leaf holding a larger quantity is
    // re-summed in u128 out of line.
    #[inline(always)]
    fn leaf_sums(&self, values: &[u64; NUM_CHILDREN]) -> Option<(u64, u64)> {
        #[cfg(all(target_arch = "x86_64", not(miri)))]
        let (qty, weighted) = if self.has_avx512 {
            unsafe { leaf_sums_avx512(values) }
        } else if self.has_avx2 {
            unsafe { leaf_sums_avx2(values) }
        } else {
            leaf_sums_scalar(values)
        };
        #[cfg(not(all(target_arch = "x86_64", not(miri))))]
        let (qty, weighted) = leaf_sums_scalar(values);
        if likely(qty != LEAF_SUM_INEXACT) {
            Some((qty, weighted))
        } else {
            leaf_sums_wide(values)
        }
    }

    #[inline(always)]
    fn prefetch_leaf(&self, leaf_idx: u32) {
        // A prefetch never faults, so no bounds check: only skip the null
        // sentinel (a constant compare) to avoid a pointless wild prefetch.
        if leaf_idx != u32::MAX {
            prefetch_read(
                self.leaf_arena.as_ptr().wrapping_add(leaf_idx as usize),
                Locality::L1,
            );
        }
    }

    // Write-intent prefetch for a leaf about to be consumed. This is
    // `prefetchw` (line arrives owned, skipping the later RFO) only when the
    // build enables `prfchw`, e.g. `-C target-cpu=native`; on baseline x86-64
    // LLVM lowers it to the same `prefetcht0` as `prefetch_leaf`.
    #[inline(always)]
    fn prefetch_leaf_w(&self, leaf_idx: u32) {
        if leaf_idx != u32::MAX {
            let leaf = self.leaf_arena.as_ptr().wrapping_add(leaf_idx as usize);
            prefetch_write(leaf.cast_mut(), Locality::L1);
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
                // Trie exhausted. Every preempt key is above every trie key,
                // so fill the rest of the order straight from the preempt tier
                // in key order (the pinned u32::MAX level included) instead of
                // refilling the trie first: work stays proportional to the
                // levels consumed, with no refill burst.
                while shares_to_buy > 0 {
                    let Some(&k) = self.preempt_keys.first() else {
                        break;
                    };
                    let Some(avail) = self.preempt.get_mut(&k) else {
                        invariant_violated("preempt key index names a key missing from the map");
                    };
                    let take = (*avail).min(shares_to_buy);
                    total_cost = total_cost.saturating_add((k as u64).saturating_mul(take));
                    shares_to_buy -= take;
                    *avail -= take;
                    if *avail == 0 {
                        self.preempt_remove(k);
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
            // `None` means the leaf holds more than any u64 order: partial.
            if let Some((qty_total, weighted)) =
                self.leaf_sums(&self.leaf_arena[leaf_idx as usize].values)
                && qty_total <= shares_to_buy
            {
                // Consume the entire leaf.
                total_cost = total_cost
                    .saturating_add(base.saturating_mul(qty_total))
                    .saturating_add(weighted);
                shares_to_buy -= qty_total;
                self.remove_min_leaf(leaf_idx, mask);
            } else {
                // Partial: walk set bits from the cheapest slot up.
                let leaf = &mut self.leaf_arena[leaf_idx as usize];
                let mut consumed_slots = 0u32;
                while shares_to_buy > 0 {
                    // The leaf holds more than the order, so a set bit remains.
                    if unlikely(leaf.mask == 0) {
                        invariant_violated("partial buy ran out of levels in its leaf");
                    }
                    let slot = tz64(leaf.mask);
                    let price = base | slot as u64;
                    let qty = leaf.values[slot];
                    if qty <= shares_to_buy {
                        total_cost = total_cost.saturating_add(price.saturating_mul(qty));
                        shares_to_buy -= qty;
                        leaf.values[slot] = 0;
                        leaf.mask = clear_lowest_bit(leaf.mask);
                        consumed_slots += 1;
                    } else {
                        total_cost = total_cost.saturating_add(price.saturating_mul(shares_to_buy));
                        leaf.values[slot] -= shares_to_buy;
                        shares_to_buy = 0;
                    }
                }
                let partial = (base >> BITS_PER_LEVEL) as u32;
                let new_min_slot = tz64(self.leaf_arena[leaf_idx as usize].mask) as u32;
                self.min_key.set((base as u32) | new_min_slot);
                if consumed_slots > 0 {
                    self.decrement_ancestor_counts(partial, consumed_slots);
                }
                break;
            }
        }

        self.refill_if_low();
        total_cost
    }

    // Unlink and free the current minimum leaf whose (pre-consumption)
    // occupancy mask is `mask`. Ancestor counts, the leaf list, the intrusive
    // hash table, min/max bookkeeping and the cached path are all maintained.
    fn remove_min_leaf(&mut self, leaf_idx: u32, mask: u64) {
        let n = mask.count_ones();
        let (partial, next_l) = {
            let leaf = &mut self.leaf_arena[leaf_idx as usize];
            let p = leaf.ht_k;
            let nl = leaf.next_leaf;
            // No need to zero `values`: the free list re-initializes a
            // reused leaf with `LeafNode::new()`.
            leaf.mask = 0;
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
            let slot = tz64(nleaf.mask) as u32;
            self.min_key.set((nleaf.ht_k << BITS_PER_LEVEL) | slot);
        } else {
            self.min_key.set(u32::MAX);
        }
        self.detach_leaf_from_trie(leaf_idx, partial, n);
    }

    // Mirror of remove_min_leaf for the maximum leaf (sell-side consumption).
    fn remove_max_leaf(&mut self, leaf_idx: u32, mask: u64) {
        let n = mask.count_ones();
        let (partial, prev_l) = {
            let leaf = &mut self.leaf_arena[leaf_idx as usize];
            let p = leaf.ht_k;
            let pl = leaf.prev_leaf;
            // No need to zero `values`: the free list re-initializes a
            // reused leaf with `LeafNode::new()`.
            leaf.mask = 0;
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
            let slot = high_bit(pleaf.mask) as u32;
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
        let mut node_idx = ROOT;
        for (l, entry) in path.iter_mut().enumerate() {
            let shift = (NUM_LEVELS - 2 - l) * BITS_PER_LEVEL;
            let slot = ((partial >> shift) & 0x3F) as usize;
            *entry = (node_idx, slot);
            let next = self.arena[node_idx as usize].children[slot];
            self.arena[node_idx as usize].count -= n;
            node_idx = next;
        }
        debug_assert_eq!(node_idx, leaf_idx);
        self.prune_empty_path(&path);

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

    // Unlinks the emptied leaf at the end of `path` (the (node, child slot)
    // pairs from the root down) and frees every ancestor left with no
    // children. The root is never freed.
    #[inline(always)]
    fn prune_empty_path(&mut self, path: &[(u32, usize); NUM_LEVELS - 1]) {
        for (l, &(node_idx, slot)) in path.iter().enumerate().rev() {
            let node = &mut self.arena[node_idx as usize];
            node.children[slot] = u32::MAX;
            node.mask &= !(1u64 << slot);
            if node.mask != 0 || l == 0 {
                break;
            }
            self.free_list.push(node_idx);
        }
    }

    #[inline(always)]
    fn decrement_ancestor_counts(&mut self, partial: u32, n: u32) {
        let mut node_idx = ROOT;
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
                if let Some((qty_total, weighted)) = self.leaf_sums(&leaf.values)
                    && qty_total <= target_shares
                {
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
                let slot = tz64(mask);

                let price = base | slot as u64;
                let qty = leaf.values[slot];
                let buy = qty.min(target_shares);
                total_cost = total_cost.saturating_add(price.saturating_mul(buy));
                target_shares -= buy;

                if target_shares == 0 {
                    return total_cost;
                }

                mask = clear_lowest_bit(mask);
            }
            curr_leaf_idx = leaf.next_leaf;
        }

        for &k in &self.preempt_keys {
            if target_shares == 0 {
                break;
            }
            let buy = preempt_qty(&self.preempt, k).min(target_shares);
            total_cost = total_cost.saturating_add((k as u64).saturating_mul(buy));
            target_shares -= buy;
        }
        total_cost
    }

    /// Executes a market sell: consumes `shares_to_sell` from the *highest*
    /// levels downward, deleting depleted levels, and returns the total
    /// proceeds (saturating). The mirror of [`Glass::buy_shares`] — use it
    /// when this glass holds the bid side of a book.
    ///
    /// The overflow tier holds the highest prices, so it is drained first
    /// (from the top of its key index), then trie leaves are consumed whole from the
    /// max leaf backward. Note the preemption design keeps the *lowest* keys
    /// in the fast trie; for a sell-heavy workload against a book deeper than
    /// 4096 levels, consider storing negated prices (`!price`) and using the
    /// buy-side operations instead, so the best bids live in the trie.
    pub fn sell_shares(&mut self, mut shares_to_sell: u64) -> u64 {
        let mut total_proceeds = 0u64;

        // 1. Overflow tier, highest price first.
        while shares_to_sell > 0 {
            let Some(&k) = self.preempt_keys.last() else {
                break;
            };
            let Some(avail) = self.preempt.get_mut(&k) else {
                invariant_violated("preempt key index names a key missing from the map");
            };
            let take = (*avail).min(shares_to_sell);
            total_proceeds = total_proceeds.saturating_add((k as u64).saturating_mul(take));
            shares_to_sell -= take;
            *avail -= take;
            if *avail == 0 {
                self.preempt_remove(k);
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
            // `None` means the leaf holds more than any u64 order: partial.
            if let Some((qty_total, weighted)) =
                self.leaf_sums(&self.leaf_arena[leaf_idx as usize].values)
                && qty_total <= shares_to_sell
            {
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
                    // The leaf holds more than the order, so a set bit remains.
                    if unlikely(leaf.mask == 0) {
                        invariant_violated("partial sell ran out of levels in its leaf");
                    }
                    let slot = high_bit(leaf.mask);
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
                let new_max_slot = high_bit(self.leaf_arena[leaf_idx as usize].mask) as u32;
                self.max_key.set((base as u32) | new_max_slot);
                if consumed_slots > 0 {
                    self.decrement_ancestor_counts(partial, consumed_slots);
                }
                break;
            }
        }
        self.refill_if_low();
        total_proceeds
    }

    /// Estimates the proceeds of selling `target_shares` into the highest
    /// levels downward without mutating the book (saturating arithmetic).
    /// The mirror of [`Glass::compute_buy_cost`].
    pub fn compute_sell_cost(&self, mut target_shares: u64) -> u64 {
        let mut total_proceeds = 0u64;

        // Overflow tier first: it holds the highest prices.
        for &k in self.preempt_keys.iter().rev() {
            if target_shares == 0 {
                return total_proceeds;
            }
            let take = preempt_qty(&self.preempt, k).min(target_shares);
            total_proceeds = total_proceeds.saturating_add((k as u64).saturating_mul(take));
            target_shares -= take;
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
                if let Some((qty_total, weighted)) = self.leaf_sums(&leaf.values)
                    && qty_total <= target_shares
                {
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
                let slot = high_bit(mask);
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
        let mut node_idx = ROOT;
        let mut leaf_idx = u32::MAX;

        if let Some(l_idx) = self.find_leaf(partial) {
            leaf_idx = l_idx;
        }

        if leaf_idx != u32::MAX {
            if let Some(lk) = self.cached_last_key.get() {
                let depth = self.get_common_prefix_depth(key, lk);
                level = (self.cached_d.get() as usize).min(depth);
                if level > 0 && level < NUM_LEVELS - 1 {
                    node_idx = self.cached_path[level].get();
                }
            }

            for l in level..NUM_LEVELS - 1 {
                self.cached_path[l].set(node_idx);
                let shift = (NUM_LEVELS - 1 - l) * BITS_PER_LEVEL;
                let child_slot = ((key >> shift) & 0x3F) as usize;
                node_idx = self.arena[node_idx as usize].children[child_slot];
            }
            let leaf = &mut self.leaf_arena[leaf_idx as usize];
            let leaf_slot = (key & 0x3F) as usize;
            if leaf.values[leaf_slot] == 0 {
                leaf.mask |= 1u64 << leaf_slot;
                for l in 0..NUM_LEVELS - 1 {
                    let ancestor_idx = self.cached_path[l].get();
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
                    node_idx = self.cached_path[level].get();
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
                self.cached_path[l].set(node_idx);
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
                    self.arena[node_idx as usize].children[child_slot] = new_idx;
                    self.arena[node_idx as usize].mask |= 1u64 << child_slot;
                }
                self.cached_path[l].set(node_idx);
                node_idx = self.arena[node_idx as usize].children[child_slot];
            }
        }

        let leaf = &mut self.leaf_arena[leaf_idx as usize];
        let leaf_slot = (key & 0x3F) as usize;

        if leaf.values[leaf_slot] == 0 {
            leaf.mask |= 1u64 << leaf_slot;
            for l in 0..NUM_LEVELS - 1 {
                let ancestor_idx = self.cached_path[l].get();
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

    // From internal node `node_idx` at trie level `level`, descend to its
    // rightmost (`rightmost`) or leftmost leaf. Every node on a live path has
    // a non-empty mask.
    #[inline(always)]
    fn descend_to_edge_leaf(&self, mut node_idx: u32, level: usize, rightmost: bool) -> u32 {
        for _ in level..NUM_LEVELS - 1 {
            let node = &self.arena[node_idx as usize];
            let slot = if rightmost {
                find_prev_set_bit(node.mask, NUM_CHILDREN)
            } else {
                find_next_set_bit(node.mask, 0)
            };
            let Some(slot) = slot else {
                invariant_violated("empty internal node on a live trie path");
            };
            node_idx = node.children[slot];
        }
        node_idx
    }

    #[inline(always)]
    fn find_neighbor_leaves(&self, key: u32) -> (u32, u32) {
        let mut prev = u32::MAX;
        let mut next = u32::MAX;

        let mut node_idx = ROOT;
        for depth in 0..NUM_LEVELS - 1 {
            let node = &self.arena[node_idx as usize];
            let shift = (NUM_LEVELS - 1 - depth) * BITS_PER_LEVEL;
            let slot = ((key >> shift) & 0x3F) as usize;

            if let Some(p_slot) = find_prev_set_bit(node.mask, slot) {
                prev = self.descend_to_edge_leaf(node.children[p_slot], depth + 1, true);
            }
            if let Some(n_slot) = find_next_set_bit(node.mask, slot + 1) {
                next = self.descend_to_edge_leaf(node.children[n_slot], depth + 1, false);
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

        let mut node_idx = ROOT;
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
            self.prune_empty_path(&path);
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

    // The k-th smallest trie key: descend by subtree counts, then select the
    // k-th set bit of the leaf. The counting paths (popcount per leaf child,
    // then the select) are compiled as whole `target_feature` kernels:
    // on baseline x86-64 `count_ones` is a ~12-instruction software popcount,
    // and a dispatched intrinsic would be an out-of-line call per bit op.
    #[inline(always)]
    fn glass_find_kth_key(&self, k: usize) -> Option<u32> {
        #[cfg(target_arch = "x86_64")]
        {
            if self.has_fast_pdep {
                return unsafe { self.glass_find_kth_key_bmi2(k) };
            }
            if self.has_popcnt {
                return unsafe { self.glass_find_kth_key_popcnt(k) };
            }
        }
        self.glass_find_kth_key_impl::<false>(k)
    }

    #[cfg(target_arch = "x86_64")]
    #[target_feature(enable = "popcnt,bmi1,bmi2")]
    fn glass_find_kth_key_bmi2(&self, k: usize) -> Option<u32> {
        self.glass_find_kth_key_impl::<true>(k)
    }

    #[cfg(target_arch = "x86_64")]
    #[target_feature(enable = "popcnt")]
    fn glass_find_kth_key_popcnt(&self, k: usize) -> Option<u32> {
        self.glass_find_kth_key_impl::<false>(k)
    }

    #[inline(always)]
    fn glass_find_kth_key_impl<const PDEP: bool>(&self, mut k: usize) -> Option<u32> {
        if k >= self.glass_size() {
            return None;
        }
        let mut node_idx = ROOT;
        let mut key = 0u32;
        for depth in 0..NUM_LEVELS - 1 {
            let node = &self.arena[node_idx as usize];
            let mut start = 0;
            loop {
                let slot = find_next_set_bit(node.mask, start)?;
                let child_idx = node.children[slot];
                let count = if depth == NUM_LEVELS - 2 {
                    self.leaf_arena[child_idx as usize].mask.count_ones() as usize
                } else {
                    self.arena[child_idx as usize].count as usize
                };
                if k < count {
                    key |= (slot as u32) << ((NUM_LEVELS - 1 - depth) * BITS_PER_LEVEL);
                    node_idx = child_idx;
                    break;
                }
                k -= count;
                start = slot + 1;
            }
        }
        let leaf = &self.leaf_arena[node_idx as usize];
        // The descent guarantees k < popcount(leaf.mask).
        #[cfg(target_arch = "x86_64")]
        if PDEP {
            // SAFETY: only instantiated inside the bmi1+bmi2 kernel.
            return Some(key | unsafe { select_kth_set_bit_pdep(leaf.mask, k as u32) } as u32);
        }
        Some(key | select_kth_set_bit(leaf.mask, k as u32) as u32)
    }

    #[inline(always)]
    fn glass_min(&self) -> Option<(u32, u64)> {
        let leaf_idx = self.min_leaf.get();
        if leaf_idx != u32::MAX {
            let leaf = &self.leaf_arena[leaf_idx as usize];
            let slot = tz64(leaf.mask);
            return Some(leaf.level(slot));
        }
        None
    }

    #[inline(always)]
    fn glass_max(&self) -> Option<(u32, u64)> {
        let leaf_idx = self.max_leaf.get();
        if leaf_idx != u32::MAX {
            let leaf = &self.leaf_arena[leaf_idx as usize];
            let slot = high_bit(leaf.mask);
            return Some(leaf.level(slot));
        }
        None
    }

    #[inline(always)]
    fn glass_find_extreme(&self, is_min: bool) -> Option<(u32, u64)> {
        if self.arena[ROOT as usize].mask == 0 {
            return None;
        }
        let mut node_idx = ROOT;
        let mut key = 0u32;
        for depth in 0..NUM_LEVELS - 1 {
            let node = &self.arena[node_idx as usize];
            let idx = if is_min {
                find_next_set_bit(node.mask, 0)
            } else {
                find_prev_set_bit(node.mask, NUM_CHILDREN)
            }?;
            self.cached_path[depth].set(node_idx);
            key |= (idx as u32) << ((NUM_LEVELS - 1 - depth) * BITS_PER_LEVEL);
            node_idx = node.children[idx];
        }
        let leaf_idx = node_idx;
        let leaf = &self.leaf_arena[leaf_idx as usize];
        let idx = if is_min {
            find_next_set_bit(leaf.mask, 0)
        } else {
            find_prev_set_bit(leaf.mask, NUM_CHILDREN)
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
}

// Bit scans use the plain integer methods on purpose. The crate is built for
// baseline x86-64, where a BMI/LZCNT/POPCNT intrinsic cannot be inlined into
// a non-`target_feature` caller: runtime-dispatching to one costs an
// out-of-line call per scan. `trailing_zeros`/`leading_zeros` lower to inline
// `bsf`/`bsr` (the zero check folds away where the caller already tested the
// mask), which measured 29-46% fewer cycles on the cost estimators. Build with
// `-C target-cpu=native` to get tzcnt/lzcnt/blsr/popcnt.

// Index of the lowest set bit (64 for 0).
#[inline(always)]
fn tz64(mask: u64) -> usize {
    mask.trailing_zeros() as usize
}

// Clears the lowest set bit.
#[inline(always)]
fn clear_lowest_bit(mask: u64) -> u64 {
    mask & mask.wrapping_sub(1)
}

// Index of the highest set bit. `mask` must be non-zero.
#[inline(always)]
fn high_bit(mask: u64) -> usize {
    63 - mask.leading_zeros() as usize
}

// Lowest set bit at or above `start`.
#[inline(always)]
fn find_next_set_bit(mask: u64, start: usize) -> Option<usize> {
    if start >= NUM_CHILDREN {
        return None;
    }
    let mask = mask >> start;
    if mask == 0 {
        return None;
    }
    Some(start + tz64(mask))
}

// Highest set bit below `end` (`end` <= 64).
#[inline(always)]
fn find_prev_set_bit(mut mask: u64, end: usize) -> Option<usize> {
    if end < 64 {
        mask &= (1u64 << end) - 1;
    }
    if mask == 0 {
        return None;
    }
    Some(high_bit(mask))
}

// Every quantity below this bound makes a leaf's wrapping sums exact:
// sum(qty) <= 64 * (2^52 - 1) < 2^58 and sum(slot * qty) <= 63 * sum(qty) < 2^64.
const LEAF_SUM_EXACT_BOUND: u64 = 1 << 52;
// Returned as sum(qty) when some quantity reaches LEAF_SUM_EXACT_BOUND (an
// exact sum is below 2^58, so it cannot collide). Keeps the result of the
// out-of-line AVX-512 call in two registers instead of a stack-returned triple.
const LEAF_SUM_INEXACT: u64 = u64::MAX;

// (sum(qty), sum(slot * qty)) over the 64 slots with wrapping sums, or
// (LEAF_SUM_INEXACT, _) when a quantity reaches LEAF_SUM_EXACT_BOUND and the
// sums might have wrapped (see `Glass::leaf_sums`). Empty slots are 0 and
// contribute nothing.
#[inline(always)]
fn leaf_sums_scalar(values: &[u64; NUM_CHILDREN]) -> (u64, u64) {
    let mut qty = 0u64;
    let mut weighted = 0u64;
    let mut any = 0u64;
    for (i, &v) in values.iter().enumerate() {
        qty = qty.wrapping_add(v);
        weighted = weighted.wrapping_add((i as u64).wrapping_mul(v));
        any |= v;
    }
    if any < LEAF_SUM_EXACT_BOUND {
        (qty, weighted)
    } else {
        (LEAF_SUM_INEXACT, weighted)
    }
}

// Exact leaf sums for a leaf holding a quantity >= LEAF_SUM_EXACT_BOUND:
// `None` if sum(qty) exceeds u64, else (sum(qty), sum(slot * qty) saturated).
// u128 cannot overflow here: sum(slot * qty) < 63 * 64 * 2^64 < 2^76.
#[cold]
#[inline(never)]
fn leaf_sums_wide(values: &[u64; NUM_CHILDREN]) -> Option<(u64, u64)> {
    let mut qty = 0u128;
    let mut weighted = 0u128;
    for (i, &v) in values.iter().enumerate() {
        qty += v as u128;
        weighted += i as u128 * v as u128;
    }
    let qty = u64::try_from(qty).ok()?;
    Some((qty, u64::try_from(weighted).unwrap_or(u64::MAX)))
}

// The scalar leaf sums, auto-vectorized for AVX2 (4 x u64 lanes).
#[cfg(all(target_arch = "x86_64", not(miri)))]
#[target_feature(enable = "avx2")]
fn leaf_sums_avx2(values: &[u64; NUM_CHILDREN]) -> (u64, u64) {
    leaf_sums_scalar(values)
}

// Index of the k-th (0-based) set bit of `mask`; requires k < popcount(mask).
#[inline(always)]
fn select_kth_set_bit(mask: u64, k: u32) -> usize {
    let mut m = mask;
    for _ in 0..k {
        m = clear_lowest_bit(m);
    }
    tz64(m)
}

// The same via PDEP: deposit a unit bit into the k-th set position, then
// count trailing zeros (two instructions). Used only where PDEP is hardware
// (`pdep_is_microcoded`).
#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "bmi1,bmi2")]
#[inline]
fn select_kth_set_bit_pdep(mask: u64, k: u32) -> usize {
    _tzcnt_u64(_pdep_u64(1u64 << k, mask)) as usize
}

// Dense-leaf extraction: for each 8-slot chunk, the corresponding byte of
// the occupancy bitmap is the k-mask, and vpcompressq packs the live values
// (and their slot indices) densely — no per-bit scanning. Slots and values
// land in stack scratch, then the requested prefix is pushed as tuples.
#[cfg(all(target_arch = "x86_64", not(miri)))]
#[target_feature(enable = "avx512f,avx512dq")]
fn extract_leaf_avx512(leaf: &LeafNode, base: u32, need: usize, out: &mut Vec<(u32, u64)>) {
    unsafe {
        let mut slots = [0u64; NUM_CHILDREN];
        let mut vals = [0u64; NUM_CHILDREN];
        let mut cnt = 0usize;
        let mut idx = _mm512_setr_epi64(0, 1, 2, 3, 4, 5, 6, 7);
        let eight = _mm512_set1_epi64(8);
        for chunk in 0..NUM_CHILDREN / 8 {
            let m8 = ((leaf.mask >> (chunk * 8)) & 0xFF) as u8;
            if m8 != 0 {
                let v = _mm512_loadu_si512(leaf.values.as_ptr().add(chunk * 8) as *const _);
                _mm512_mask_compressstoreu_epi64(vals.as_mut_ptr().add(cnt) as *mut _, m8, v);
                _mm512_mask_compressstoreu_epi64(slots.as_mut_ptr().add(cnt) as *mut _, m8, idx);
                cnt += m8.count_ones() as usize;
            }
            idx = _mm512_add_epi64(idx, eight);
        }
        for i in 0..need.min(cnt) {
            out.push((base | slots[i] as u32, vals[i]));
        }
    }
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
        let mut any = _mm512_setzero_si512();
        let mut idx = _mm512_setr_epi64(0, 1, 2, 3, 4, 5, 6, 7);
        let eight = _mm512_set1_epi64(8);
        for chunk in 0..NUM_CHILDREN / 8 {
            let v = _mm512_loadu_si512(values.as_ptr().add(chunk * 8) as *const _);
            qty = _mm512_add_epi64(qty, v);
            weighted = _mm512_add_epi64(weighted, _mm512_mullo_epi64(v, idx));
            any = _mm512_or_si512(any, v);
            idx = _mm512_add_epi64(idx, eight);
        }
        // One vptestmq against the bits >= LEAF_SUM_EXACT_BOUND instead of a
        // horizontal OR reduction.
        let high = _mm512_set1_epi64(!(LEAF_SUM_EXACT_BOUND - 1) as i64);
        let qty = if _mm512_test_epi64_mask(any, high) == 0 {
            _mm512_reduce_add_epi64(qty) as u64
        } else {
            LEAF_SUM_INEXACT
        };
        (qty, _mm512_reduce_add_epi64(weighted) as u64)
    }
}

/// Ascending iterator over `(price, quantity)` levels; see [`Glass::iter`].
pub struct Iter<'a> {
    glass: &'a Glass,
    leaf_idx: u32,
    mask: u64,
    preempt: btree_set::Range<'a, u32>,
}

impl Iterator for Iter<'_> {
    type Item = (u32, u64);

    fn next(&mut self) -> Option<(u32, u64)> {
        while self.leaf_idx != u32::MAX {
            if self.mask != 0 {
                let slot = tz64(self.mask);
                self.mask = clear_lowest_bit(self.mask);
                let leaf = &self.glass.leaf_arena[self.leaf_idx as usize];
                return Some(leaf.level(slot));
            }
            self.leaf_idx = self.glass.leaf_arena[self.leaf_idx as usize].next_leaf;
            if self.leaf_idx != u32::MAX {
                self.mask = self.glass.leaf_arena[self.leaf_idx as usize].mask;
            }
        }
        // Overflow tier, in key order.
        let &k = self.preempt.next()?;
        Some((k, preempt_qty(&self.glass.preempt, k)))
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
