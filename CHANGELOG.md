# Changelog

## Unreleased

- **Fix: leaf-sum overflow.** `leaf_sums` wrapped mod 2^64, so a leaf (64
  adjacent prices) whose quantities summed past `u64` sent `buy_shares`,
  `sell_shares`, `compute_buy_cost` and `compute_sell_cost` down the
  whole-leaf path with a wrong cost, and the executors deleted levels the
  order never reached (e.g. buying 10 from `{10:5, 64:2^63, 65:2^63}` cost
  9223372036854775858 instead of 370 and emptied the book). `leaf_sums` now
  returns exact totals or `None`: the SIMD pass is exact while every quantity
  is below 2^52 (one `vptestmq`), anything larger is re-summed in `u128` out
  of line. Regression tests + an exact-oracle randomized test.
- **Nightly toolchain** (`rust-toolchain.toml`): `likely`/`unlikely` hints are
  always on (measured 1-5% on the routing and sweep paths), and leaf
  prefetches use the portable `core::hint::prefetch_*`, so aarch64 gets them
  too. The `nightly` cargo feature is kept as a deprecated no-op.
- **Bit scans inline**: `tz64`/`high_bit`/`clear_lowest_bit` and popcounts use the
  integer methods instead of runtime-dispatched BMI/LZCNT/POPCNT intrinsics,
  which could not inline into the baseline-x86-64 callers and cost a call per
  scan: `compute_buy_cost` -33% cycles, deep estimate -29%.
- **AVX2 leaf sums** for CPUs without AVX-512: 23-40% faster deep sweeps
  than the scalar reduction (measured with AVX-512 disabled).
- **No bare `unwrap` in library code; broken invariants fail loudly**:
  `invariant_violated(&str) -> !` panics in every build with a message naming
  the invariant, at the point of detection.
- **Deep-book latency fix**: on a book deeper than 4096 levels, every trie
  removal re-sorted the whole preempt map (`restructure` ran per removal and
  `preempt_insert` dirtied the sorted-key cache even on quantity overwrites):
  ~830k cycles per op on a 12k-level churn workload. The preempt tier stays
  the paper's hash table (quantity updates are one hash write; a `BTreeMap`
  measured 9x slower there) plus an ordered `BTreeSet` index of its key set,
  touched only when a level appears or disappears. Once the trie is 32
  levels short, a mutating call pulls at most 32 of the lowest keys off the
  index (O(log p) each), so no operation is O(p) and no refill is unbounded:
  after a big sweep the trie is topped up 32 levels per later call, and a buy
  sweep that empties the trie fills the rest straight from the preempt tier.
  On a 12k-level book, p99.99 per-op latency fell from
  ~180k to ~16-22k TSC ticks and the worst op from ~640k to ~50-100k (the
  rest is hashbrown's own in-place rehash; the map keeps 2x capacity so it
  never grows mid-stream). The lazily sorted key cache, its dirty flag, the
  lazy bounds and the last `UnsafeCell` are gone.
- **`remove_by_index`**: the rank descent runs as one POPCNT(+BMI2) kernel
  (-22% cycles); PDEP is used only where it is hardware (not AMD before Zen 3
  or Hygon, where it is microcoded).
- **Toolchain pinned** to `nightly-2026-09-25`.
- **Cleanup**: removed never-read `parent` fields and a no-op padding field,
  the always-zero `root` field (now `ROOT`), every `UnsafeCell`
  (`cached_path` is `[Cell<u32>; 5]`), and 512-byte leaf zeroing on free that
  reuse redoes; shared prune/level helpers; corrected comments (the write prefetch is `prefetchw` only with
  `prfchw` enabled).
- **Benchmarks**: the setup-based benches (buy/sell shares, remove by index)
  no longer time dropping the book (their routines return it so criterion
  drops it outside the timed region), and the key/value generators use fixed
  seeds. This removes most of the old 1k-share buy/sell "speedup" (it was the
  `BTreeMap`'s drop time); deep buy/sell now measure 17.7x / 29.8x. README
  table regenerated (best of two pinned runs, `latency-performance`).

- `top_levels(n, &mut buf)`: allocation-free best-N snapshot for imbalance
  computation; ~1.5x faster than `BTreeMap` at depth 25, with AVX-512
  `vpcompressq` whole-leaf extraction (occupancy bitmap as lane mask) for
  bulk depths.
- PDEP-based O(1) k-th set-bit select in the rank/select descent
  (`remove_by_index`): ~17-20% faster random-index drains, runtime-gated on
  BMI2 (portable loop fallback elsewhere).

- **Sell side**: `sell_shares` and `compute_sell_cost` — market-sell
  execution/estimation from the highest price downward (bid-book mirror of
  the buy path), with whole-leaf vectorized consumption and overflow-tier
  draining; deep-sweep benchmarks included.
- **BTreeMap-style API**: `contains_key`, `get_key_value`,
  `first_key_value`/`last_key_value`, `pop_first`/`pop_last`,
  `keys`/`values`, `range` (full `RangeBounds`), `retain`, `split_off`,
  owning `IntoIterator`, and `next_level`/`prev_level` (the paper's
  next/prev). `get_mut`/`entry` are intentionally omitted; `update_value`
  is the invariant-safe in-place adjust.
- Dev-dependency bumps: criterion 0.8, rand 0.10.

## 0.1.0 — 2026-07-15

### Fixed (audited against arXiv:2506.13991)

- **Bounded hash-table probe is now tri-state** (paper §5.2): a chain longer
  than 5 links answers "don't know" and falls back to a trie descent. Keys
  whose bucket chain overflowed were previously invisible to
  `get`/`remove`/`update_value`.
- **Eager preemption threshold** (paper §4.5): the threshold and overflow-tier
  bounds are maintained exactly on every preemption/removal. A stale threshold
  previously misrouted lookups after an eviction and could duplicate a key in
  both tiers.
- `update_value` reaching zero now removes the level instead of corrupting
  occupancy invariants.
- `min`/`max` sentinel collisions fixed for boundary keys `0` and `u32::MAX`;
  `u32::MAX` is pinned to the overflow tier (the threshold's saturation
  point) so it always remains routable.

### Performance

- Leaf-wise `buy_shares`: consumes 64 price levels per step (one vectorized
  sum + one ancestor walk) instead of a min/remove/restructure cycle per
  level; ~13x over `BTreeMap` on deep sweeps.
- `compute_buy_cost`: vectorized whole-leaf fast path for deep sweeps (~7x).
- AVX-512F/DQ leaf reductions, hardware POPCNT dispatch (~10-15% on
  `remove_by_index`), next-leaf prefetch; all runtime-detected.
- `insert` overwrite path specialized (single routing + lookup).
- Repo builds with the Intel JCC-erratum mitigation flag
  (`.cargo/config.toml`), which measured +16-35% on hot paths on
  Skylake-SP/Cascade Lake and stabilizes timings across rebuilds.

### Added

- `len`, `is_empty`, `clear`, ascending `iter()` (+ `IntoIterator for
  &Glass`), `Debug`, `FromIterator`, `Extend`.
- 200k-op randomized differential test suite vs `BTreeMap` plus regression
  tests for all fixed bugs; deep-sweep benchmarks.
- Full rustdoc, portable (non-x86_64) build support with runtime feature
  detection, CI (test/lint/aarch64 check), `examples/demo.rs`.

## 0.0.2

- Dual-arena trie with linked leaf list, cached path, intrusive hash-table
  cache, preemption tier.
