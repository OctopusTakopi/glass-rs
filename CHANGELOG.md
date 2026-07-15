# Changelog

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
