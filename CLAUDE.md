# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project

Rust implementation of the "glass" data structure from [arXiv:2506.13991](https://arxiv.org/abs/2506.13991) (Viktor Krapivensky) — a trie-based ordered set of `u32 -> u64` (price -> quantity) tuned for client-side order books. Ported from the C reference at [shdown/glass-paper](https://github.com/shdown/glass-paper). Optimized and benchmarked on an Intel Xeon Gold 6230; the README's benchmark table reflects that machine.

## Commands

```bash
cargo test                          # all 20 unit tests (fast, <1s)
cargo test test_buy_shares          # single test by name
cargo run                           # src/main.rs demo of the public API
cargo bench                         # full criterion suite, ~6s measurement per bench, very slow overall
cargo bench -- buy_shares           # single benchmark by filter
cargo bench --no-run                # compile-check benches without running them
```

Benchmarks compare every operation against `std::collections::BTreeMap`; the BTreeMap baselines live in `benches/basic.rs` alongside the glass ones. For numbers that match the README, build with `RUSTFLAGS="-C target-cpu=native"`.

## Architecture

Everything is in `src/lib.rs` (~930 lines). There is no module tree — read the file top to bottom.

### Two-tier storage: trie + preempt map

`Glass` is not one container but two, and every public method routes between them via `check_bounds_and_thres(key)`:

- **The trie** ("glass") holds at most `MAX_SIZE` (4096) keys — the *lowest* keys, i.e. the best prices on the buy side. This is the fast path.
- **`preempt`**, an `AHashMap`, holds the overflow — everything at or above `thres`, where `thres` is the minimum key currently in `preempt`. Any key `>= thres` lives in the map, never the trie.

When the trie is full and a new key arrives that is better (lower) than the trie's current max, `insert` evicts that max into `preempt` and inserts the new key. `restructure()` runs the reverse: when the trie drops below `MAX_SIZE`, it pulls the lowest preempt keys back into the trie. The tier invariant is strict: every trie key < `thres` = min preempt key, so `min()` is the trie min whenever the trie is non-empty, and `max()` is the preempt max whenever the map is non-empty.

Threshold maintenance is **eager** (paper §4.5): `preempt_insert`/`preempt_remove` keep `thres`/`preempt_min`/`preempt_max` exact on every mutation; bounds only go invalid when a boundary key is removed from the map, and `check_bounds_and_thres` recomputes on the next call whenever `preempt_bounds_valid` is false. Do not add a preempt mutation that bypasses these helpers — a stale `thres` misroutes keys between tiers (this was a real bug, fixed 2026-07; see `tests/differential.rs::thres_stays_correct_after_eviction`).

**Key `u32::MAX` is pinned to the preempt tier** — it can never satisfy `key < thres` because `thres` saturates at `u32::MAX` (the paper's "∞"). `restructure` deliberately never moves it into the trie, and `buy_shares` consumes it directly from the map as its final step.

### Trie layout: dual arena

36 bits (`PAD_BITS` 4 + 32-bit key) / `BITS_PER_LEVEL` 6 = `NUM_LEVELS` 6 levels, 64 children each.

- Levels 0–4 are `InternalNode` in `arena` (a `Vec`, indices are `u32`, `u32::MAX` is the null sentinel).
- Level 5 is `LeafNode` in `leaf_arena` — a separate arena so 64 sequential price levels pack into one contiguous node.
- Both arenas have free lists (`free_list`, `leaf_free_list`) rather than deallocating.

`InternalNode.count` is the number of populated leaf slots in its subtree; `arena[root].count` *is* `glass_size()`, and `glass_find_kth_key` descends by these counts. Every insert/remove that changes occupancy must fix `count` on all five ancestors — this is the invariant most likely to break.

`InternalNode.mask` / `LeafNode.mask` are 64-bit occupancy bitmaps scanned with BMI1/BMI2/LZCNT intrinsics (`find_next_set_bit`, `find_prev_set_bit`).

### Value 0 means absent

A leaf slot is occupied iff `values[slot] != 0`, mirrored by the `mask` bit. Consequently `insert(key, 0)` is a delete, `update_value` that drives a value to 0 removes the level (paper's `adjust` semantics), and `get` returns `None` for a stored zero. Zero quantity is not representable.

### Three overlapping fast paths

These accelerate lookups and must all be kept consistent on mutation:

1. **Intrusive hash table** — `ht_heads` (4096 buckets) chains `LeafNode`s through their own `ht_next`/`ht_prev` fields, keyed on `ht_k = key >> 6`. `ht_lookup` probes at most `HT_MAX_LOOKUP_LEN` (5) links and is **tri-state** (paper §5.2): `Found` / `HT_ABSENT` (chain ended within the bound — authoritative, every live leaf is chained) / `HT_UNKNOWN` (chain longer than the bound). `find_leaf` resolves `HT_UNKNOWN` via `trie_find_leaf`, a full descent kept `#[cold]` + `#[inline(never)]` so hot lookup sites stay small. All lookups must go through `find_leaf`, never `ht_lookup` directly — treating `Unknown` as `Absent` makes colliding keys (2^18 stride) silently invisible.
2. **Cached path** — `cached_last_key` + `cached_d` + `cached_path[5]` memoize the traversal to the last touched key. `get_common_prefix_depth` computes how much of that path a new key shares, and traversal resumes from there. This is what makes sequential access O(1)-ish. Whole-leaf removal (`remove_min_leaf`) must clear this cache when the cached key shared the removed leaf's partial key.
3. **Linked leaf list** — `next_leaf`/`prev_leaf` plus `min_leaf`/`max_leaf` give O(1) successor/predecessor across leaves. `buy_shares` consumes **whole leaves at a time** through this list (one vectorized sum + one ancestor-count walk per 64 price levels via `remove_min_leaf`), and `compute_buy_cost` uses per-slot scan for the first leaf but vectorized whole-leaf sums for subsequent ones.

### SIMD leaf reduction

`leaf_sums` returns `(Σ qty, Σ slot·qty)` over a leaf's 64 values; empty slots are zero so no masking is needed, and whole-leaf cost is `base·Σqty + Σ(slot·qty)`. Runtime-dispatched: `leaf_sums_avx512` (needs AVX-512F + DQ for `vpmullq`, detected into `has_avx512`) or `leaf_sums_scalar`. Inner sums wrap; callers combine with saturating arithmetic — keep that convention.

### Interior mutability and threading

Read-only methods (`get`, `min`, `max`, `compute_buy_cost`) take `&self` but still mutate caches, so nearly every hot field is a `Cell` and the collections are `UnsafeCell`. The type is therefore **single-threaded by construction** — do not add `Send`/`Sync`, and be aware that `&self` methods here are not side-effect-free.

### Platform

`use std::arch::x86_64::*` is unconditional, so the crate is **x86-64 only** and will not compile elsewhere. BMI1/BMI2/LZCNT are detected at runtime into `has_bmi1`/`has_bmi2`/`has_lzcnt`, and every intrinsic call site has a portable fallback branch — keep both arms in sync when touching bit-scan code.

## Tests

`src/tests.rs` is pulled in via `include!("tests.rs")` at the bottom of `lib.rs`, not declared as a module. It lives inside `lib.rs`'s scope on purpose: the tests assert on private internals (`glass.arena.len()`, `glass.min_key.get()`, `unsafe { &*glass.preempt.get() }`) and call private methods like `glass_insert`/`glass_remove` to exercise the trie tier directly, bypassing preempt routing. Moving these to `tests/` would break them.

Tests named `test_glass_*` target the trie tier alone; the unprefixed ones (`test_insert_and_get`, `test_restructure`, ...) exercise the public two-tier API. `test_insert_invariant_bug_repro` and `test_restructure` guard the preemption/restructure boundary at exactly 4096 keys — run them after any change to the tier-routing logic.

`tests/differential.rs` is the main safety net: a 200k-op randomized differential test against a `BTreeMap` oracle (deterministic xorshift seed, so failures reproduce), plus targeted repros for historical bugs (HT chain overflow at 2^18-strided keys, stale threshold after eviction, zero-value corruption, boundary keys `0`/`u32::MAX`). Public API only. Run it after any change to routing, lookup, or consumption logic — it crosses the 4096-key preemption boundary and the HT probe bound by construction.

## Tuning constants

At the top of `src/lib.rs`: `BITS_PER_LEVEL` (6), `MAX_SIZE` (4096, trie capacity before preemption), `HT_SIZE` (4096), `HT_MAX_LOOKUP_LEN` (5), `ARENA_CAPACITY`, `LEAF_ARENA_CAPACITY`. `BITS_PER_LEVEL` is load-bearing far beyond its declaration — `0x3F` masks, `<< 6` shifts, and `[u64; 64]` mask widths are hardcoded throughout, so it is not actually a free parameter.
