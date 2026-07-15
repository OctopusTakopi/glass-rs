# Changelog

## Unreleased

- `nightly` cargo feature: `core::hint::likely`/`unlikely` annotations on
  the hot routing branches (no-op shims on stable). Measured neutral to
  slightly positive under the JCC-mitigated build; README documents PGO as
  the principled route to layout-level gains.

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
