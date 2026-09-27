# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project

Rust implementation of the "glass" data structure from [arXiv:2506.13991](https://arxiv.org/abs/2506.13991) (Viktor Krapivensky) — a trie-based ordered set of `u32 -> u64` (price -> quantity) tuned for client-side order books. Ported from the C reference at [shdown/glass-paper](https://github.com/shdown/glass-paper). Optimized and benchmarked on an Intel Xeon Gold 6230; the README's benchmark table reflects that machine.

## Commands

The crate requires **nightly** (`rust-toolchain.toml`): `#![feature(likely_unlikely, hint_prefetch)]`.

```bash
cargo test                          # unit + differential tests (fast, ~1s)
cargo test test_buy_shares          # single test by name
cargo run --example demo            # public API demo
cargo bench                         # full criterion suite, ~6s measurement per bench, very slow overall
cargo bench -- buy_shares           # single benchmark by filter
cargo bench --no-run                # compile-check benches without running them
cargo check --target aarch64-unknown-linux-gnu   # portability check (no CI runs it)
cargo clippy --all-targets -- -D warnings && cargo fmt --check
cargo test --features check-invariants          # same, plus Glass::check_invariants every 16 ops of consuming_ops_on_sparse_books
cargo fuzz run ops                              # coverage-guided fuzzing (fuzz/, needs cargo-fuzz); add -- -len_control=0
```

Benchmarks compare every operation against `std::collections::BTreeMap`; the BTreeMap baselines live in `benches/basic.rs` alongside the glass ones.

**Benchmarking on this machine is treacherous.** The dev CPU (Xeon Gold 6230, Cascade Lake) has the Intel JCC erratum: without the `-x86-branches-within-32B-boundaries` LLVM flag (set in `.cargo/config.toml` — do not remove it), hot-loop timings swing ±40-80% between rebuilds purely from code-layout luck. Even with it, the machine has heavy ambient load. Never trust cross-run criterion deltas here: A/B by building both binaries first, then running them interleaved (min-of-N), and use `perf stat` instruction counts (deterministic) to distinguish real work from layout effects.

## Architecture

Everything is in `src/lib.rs` (with `src/tests.rs` `include!`d at its end). There is no module tree — read the file top to bottom.

### Two-tier storage: trie + preempt map

`Glass` is not one container but two, and every public method routes between them via `routes_to_trie(key)` (`key < thres`):

- **The trie** ("glass") holds at most `MAX_SIZE` (4096) keys — the *lowest* keys, i.e. the best prices on the buy side. This is the fast path.
- **The preempt tier** holds the overflow — everything at or above `thres`, the lowest preempt key (`u32::MAX` when empty). It is the paper's hash table, `preempt: AHashMap<u32, u64>` (a quantity change at an existing deep level is one O(1) hash write — keep it that way; a `BTreeMap` there measured 9x slower on deep updates), plus `preempt_keys: BTreeSet<u32>`, an ordered index of its key set touched only when a level appears or disappears. The two must always hold the same key set; `preempt_insert`/`preempt_remove` maintain both and keep `thres` exact. Do not add a preempt mutation that bypasses them — a stale `thres` misroutes keys between tiers (`tests/differential.rs::thres_stays_correct_after_eviction` guards it).

When the trie is full and a new key arrives that is better (lower) than the trie's current max, `insert` evicts that max into `preempt` and inserts the new key. `restructure()` runs the reverse, bounded: once a mutating call (insert into preempt, remove from either tier, a zeroing `update_value`, `buy_shares`/`sell_shares`) leaves the trie `REFILL_BATCH` (32) or more levels short, `refill_if_low` pulls **at most 32** of the lowest preempt keys off the index (O(log p) each). After a big sweep the trie is topped up 32 levels per later call; meanwhile the best levels are served, correctly, from the preempt tier. When a buy sweep empties the trie, `buy_shares` fills the rest straight from the preempt tier in key order rather than refilling first. Keep every refill capped — an uncapped refill after a sweep moved up to 4096 levels in one call. Nothing in the preempt tier is O(p): an earlier design scanned or sorted the whole map per refill (~200 µs per op on a 12k-level book), and do not refill after every single removal either — top-of-book churn then ping-pongs a level between the tiers per event (4x slower churn). The tier invariant is strict: every trie key < `thres` = min preempt key, so `min()` is the trie min whenever the trie is non-empty, and `max()` is the preempt max whenever the map is non-empty. The preempt map keeps `capacity >= 2 * len`, so under churn hashbrown only rehashes its tombstones in place instead of occasionally growing (a ~250 µs one-off stall).

**Key `u32::MAX` is pinned to the preempt tier** — it can never satisfy `key < thres` because `thres` saturates at `u32::MAX` (the paper's "∞"). `restructure` deliberately never moves it into the trie, and `buy_shares` consumes it directly from the map as its final step.

### Trie layout: dual arena

36 bits (`PAD_BITS` 4 + 32-bit key) / `BITS_PER_LEVEL` 6 = `NUM_LEVELS` 6 levels, 64 children each.

- Levels 0–4 are `InternalNode` in `arena` (a `Vec`, indices are `u32`, `u32::MAX` is the null sentinel).
- Level 5 is `LeafNode` in `leaf_arena` — a separate arena so 64 sequential price levels pack into one contiguous node.
- Both arenas have free lists (`free_list`, `leaf_free_list`) rather than deallocating.

`InternalNode.count` is the number of populated leaf slots in its subtree; `arena[ROOT].count` (the root is always slot 0) *is* `glass_size()`, and `glass_find_kth_key` descends by these counts. Every insert/remove that changes occupancy must fix `count` on all five ancestors — this is the invariant most likely to break.

`InternalNode.mask` / `LeafNode.mask` are 64-bit occupancy bitmaps scanned with the free functions `find_next_set_bit` / `find_prev_set_bit` / `tz64` / `high_bit` (plain `trailing_zeros`/`leading_zeros`; see below).

### Value 0 means absent

A leaf slot is occupied iff `values[slot] != 0`, mirrored by the `mask` bit. Consequently `insert(key, 0)` is a delete, `update_value` that drives a value to 0 removes the level (paper's `adjust` semantics), and `get` returns `None` for a stored zero. Zero quantity is not representable.

### Three overlapping fast paths

These accelerate lookups and must all be kept consistent on mutation:

1. **Intrusive hash table** — `ht_heads` (4096 buckets) chains `LeafNode`s through their own `ht_next`/`ht_prev` fields, keyed on `ht_k = key >> 6`. `ht_lookup` probes at most `HT_MAX_LOOKUP_LEN` (5) links and is **tri-state** (paper §5.2): `Found` / `HT_ABSENT` (chain ended within the bound — authoritative, every live leaf is chained) / `HT_UNKNOWN` (chain longer than the bound). `find_leaf` resolves `HT_UNKNOWN` via `trie_find_leaf`, a full descent kept `#[cold]` + `#[inline(never)]` so hot lookup sites stay small. All lookups must go through `find_leaf`, never `ht_lookup` directly — treating `Unknown` as `Absent` makes colliding keys (2^18 stride) silently invisible.
2. **Cached path** — `cached_last_key` + `cached_d` + `cached_path[5]` memoize the traversal to the last touched key. `get_common_prefix_depth` computes how much of that path a new key shares, and traversal resumes from there. This is what makes sequential access O(1)-ish. Any removal that frees a leaf (`glass_remove` emptying it, `detach_leaf_from_trie` for whole-leaf consumption) may free its ancestors too, so it must clear this cache whenever the cached key shared the removed leaf's partial key, not only when it equals the removed key: buy/sell consume levels without touching the cache, so it can name an already-consumed level of that leaf, and a stale path hangs the next insert under a freed node (`tests/differential.rs::path_cache_cleared_when_leaf_emptied` guards it).
3. **Linked leaf list** — `next_leaf`/`prev_leaf` plus `min_leaf`/`max_leaf` give O(1) successor/predecessor across leaves. `buy_shares` consumes **whole leaves at a time** through this list (one vectorized sum + one ancestor-count walk per 64 price levels via `remove_min_leaf`), and `compute_buy_cost` uses per-slot scan for the first leaf but vectorized whole-leaf sums for subsequent ones. The sell side (`sell_shares`/`compute_sell_cost`) mirrors this from `max_leaf` backward via `remove_max_leaf` — but drains the preempt tier **first** (it holds the highest prices), from the top of its key index. `remove_min_leaf`/`remove_max_leaf` share `detach_leaf_from_trie` for the ancestor-walk/free/cache-invalidation tail.

`next_level`/`prev_level` (the paper's next/prev) and `range`/`iter_at` also ride the leaf list; for a key whose leaf is missing they fall back to `find_neighbor_leaves`, which is safe to call read-only. The public API deliberately omits `get_mut`/`values_mut`/`entry`: a raw `&mut u64` could be written to 0 and break the occupancy invariant — `update_value` is the safe equivalent.

### SIMD leaf reduction

`leaf_sums` returns `Some((Σ qty, min(Σ slot·qty, u64::MAX)))`, exact, or `None` when Σ qty exceeds `u64` (the leaf then holds more than any order, so callers take the per-slot path). Empty slots are zero so no masking is needed, and whole-leaf cost is `base·Σqty + Σ(slot·qty)`. Every whole-leaf branch must be `if let Some((q, w)) = self.leaf_sums(..) && q <= shares` — never compare a wrapped sum: once a leaf sums past 2^64 that gives wrong costs and deletes levels (`tests/differential.rs::leaf_sum_overflow_is_exact` guards it). The SIMD pass (`leaf_sums_avx512` needs AVX-512F + DQ for `vpmullq`; `leaf_sums_avx2` is the scalar loop recompiled for AVX2; else `leaf_sums_scalar`) sums with wrapping arithmetic, which is exact while every quantity is below `LEAF_SUM_EXACT_BOUND` (2^52); otherwise it returns `LEAF_SUM_INEXACT` and the cold `leaf_sums_wide` re-sums in `u128`. The sentinel keeps the out-of-line SIMD call's result in two registers — a returned triple went through the stack and cost ~10% on deep sweeps. `test_leaf_sums_paths_agree` forces each path; callers combine with saturating arithmetic.

### Portability and dispatch conventions

All x86 intrinsics are cfg-gated (`target_arch = "x86_64"`, and `not(miri)` for SIMD); the crate must keep compiling on aarch64 (the `cargo check --target aarch64-unknown-linux-gnu` above; no CI runs it). Prefetches use the portable `core::hint::prefetch_read`/`prefetch_write`. **Do not runtime-dispatch single-instruction intrinsics**: the crate builds for baseline x86-64, and a `#[target_feature]` intrinsic cannot inline into a non-`target_feature` caller, so each `_tzcnt_u64`/`_blsr_u64`/`_lzcnt_u64` became an out-of-line call (removing them cut the cost estimators 29-33% in cycles). `tz64` / `clear_lowest_bit` / `high_bit` / `find_next_set_bit` / `find_prev_set_bit` are therefore free functions over the plain integer methods (inline `bsf`/`bsr`), and popcounts are `count_ones()`. Dispatch only whole kernels: `glass_find_kth_key` runs its whole descent as a `#[target_feature]` kernel (`popcnt,bmi1,bmi2` with PDEP select when `has_fast_pdep`, `popcnt` only when `has_popcnt`, else portable; `count_ones` alone is a ~12-instruction software popcount on baseline x86-64), and `leaf_sums` dispatches to the AVX-512/AVX2 kernels. Hot public methods are `#[inline(always)]`, but rare paths are deliberately outlined (`#[cold]`/`#[inline(never)]`: `trie_find_leaf`, `remove_zeroed_glass_value`, `insert_new_glass_key`, `leaf_sums_wide`, `invariant_violated`) to keep hot bodies small and layout-stable — keep new rare paths out of line too.

**No bare `unwrap`/`expect` in library code; broken invariants fail loudly.** Where an invariant guarantees a value (a sorted preempt key present in the map, a set bit left in a partially consumed leaf, a non-empty node on a live path), call `invariant_violated("...")`: it returns `!` and panics in every build, `#[track_caller]`, naming the invariant. Do not add "graceful" fallbacks after it — carrying on from a corrupt book hands the caller plausible wrong prices, and the fallbacks themselves corrupted the leaf list. `preempt_qty` wraps the preempt-map lookups this way.

### Interior mutability and threading

The caches (`min_key`/`max_key`, `min_leaf`/`max_leaf`, and the path cache: `cached_path` is `[Cell<u32>; 5]`) are `Cell`s because the `&self` helper `glass_find_extreme` rewrites them; it only runs under `&mut self` (from `glass_remove`), so the public `&self` methods (`get`, `min`, `max`, `compute_*_cost`, iteration) change no state. There is no `UnsafeCell`: everything else (`preempt`, `preempt_keys`, `ht_heads`, the arenas) is mutated only through `&mut self`; keep it that way. The `Cell`s make `Glass` `Send` but not `Sync`; never `unsafe impl Sync` for it.

### Runtime feature detection

`detect_features` fills `has_fast_pdep` (POPCNT + BMI1 + BMI2 and a hardware PDEP: `pdep_is_microcoded` excludes AMD before Zen 3 and Hygon, where it costs ~18-290 cycles), `has_popcnt`, `has_avx512` (F + DQ) and `has_avx2`; each dispatched kernel has a portable fallback that must stay equivalent (`test_leaf_sums_paths_agree`).

## Tests

`src/tests.rs` is pulled in via `include!("tests.rs")` at the bottom of `lib.rs`, not declared as a module. It lives inside `lib.rs`'s scope on purpose: the tests assert on private internals (`glass.arena.len()`, `glass.min_key.get()`, `glass.preempt`) and call private methods like `glass_insert`/`glass_remove` to exercise the trie tier directly, bypassing preempt routing. Moving these to `tests/` would break them.

Tests named `test_glass_*` target the trie tier alone; the unprefixed ones (`test_insert_and_get`, `test_restructure`, ...) exercise the public two-tier API. `test_insert_invariant_bug_repro` and `test_restructure` guard the preemption boundary at exactly 4096 keys and the `REFILL_BATCH` refill — run them after any change to the tier-routing logic.

`tests/differential.rs` is the main safety net: a 200k-op randomized differential test against a `BTreeMap` oracle (deterministic xorshift seed, so failures reproduce), `consuming_ops_on_sparse_books` (the consuming operations on market-shaped and scattered books), plus targeted repros for historical bugs (HT chain overflow at 2^18-strided keys, stale threshold after eviction, zero-value corruption, boundary keys `0`/`u32::MAX`, stale path cache after a leaf empties). Public API only. Run it after any change to routing, lookup, or consumption logic — it crosses the 4096-key preemption boundary and the HT probe bound by construction.

`Glass::check_invariants` (feature `check-invariants`, not in the default API) verifies the whole structure: trie masks and counts, no leaked or doubly-reachable nodes/leaves, hash chains, the ordered leaf list, min/max caches, tier split and `thres`, and that the cached path is the live path to its key. Keep it in sync with any new internal state. It turns latent corruption into an immediate failure: the stale-path-cache bug only misbehaved once a later insert used the stale path, but breaks the invariant at the removal itself.

`fuzz/` is a cargo-fuzz crate: `fuzz/src/lib.rs` (`glass_rs_fuzz::run`) replays an op list against glass-rs and a `BTreeMap` oracle with `check_invariants` after every op; `fuzz_targets/ops.rs` feeds it from libFuzzer. Keys and order sizes can be relative to the book (best keys ± d, exactly the first n levels ± d); with raw numbers only, libFuzzer never produced the 4-op trigger of the stale-path-cache bug. Coverage guidance does not help with deep, state-dependent sequences like that one; long seeded random walks with invariant checks (like `consuming_ops_on_sparse_books`) found it in a few percent of seeds. Use `-len_control=0`: the default length ramp keeps inputs too short for multi-op patterns for minutes.

## Tuning constants

At the top of `src/lib.rs`: `BITS_PER_LEVEL` (6), `MAX_SIZE` (4096, trie capacity before preemption), `HT_SIZE` (4096), `HT_MAX_LOOKUP_LEN` (5), `ARENA_CAPACITY`, `LEAF_ARENA_CAPACITY`. `BITS_PER_LEVEL` is load-bearing far beyond its declaration — `0x3F` masks, `<< 6` shifts, and `[u64; 64]` mask widths are hardcoded throughout, so it is not actually a free parameter.
