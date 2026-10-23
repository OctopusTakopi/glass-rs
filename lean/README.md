# GlassProof: Lean 4 proofs for glass-rs

Machine-checked correctness proofs for the algorithms in `../src/lib.rs`,
written against a Lean model of each Rust function (every model `def` cites
the `src/lib.rs` lines it transcribes).

```bash
cd lean && lake build     # Lean 4.32.2 (pinned in lean-toolchain), no Mathlib
```

A full build takes ~13 minutes, almost all of it one SAT query
(`Bits.select_pdep_eq_loop`); the other modules build in seconds.

No `sorry`, no `axiom` declarations, no `native_decide`. Trust base: Lean's
standard axioms (`propext`, `Classical.choice`, `Quot.sound`) plus, for
`Bits.lean` only, `bv_decide`'s SAT certificates (checked by Lean's compiled
LRAT checker rather than the kernel).

## What is proved

| Module | Result |
|---|---|
| `Tiers.lean` | **`glass_refines_map`**: for every sequence of `insert` / `remove` / `get` / `update_value` / `min` / `max` / `clear` from `Glass::new()`, each answer equals a plain map's, the tier invariant holds throughout, and the final book is the plain map's. Models the overflow tier as the hash map plus its ordered key index (same key set, strictly ascending), exact `thres`, eviction of the trie max when full, and the `REFILL_BATCH` refill loop (never moves the pinned `u32::MAX` key). `restructure_never_panics`, `minOp_lookup_present` and `maxOp_lookup_present` prove the crate's `invariant_violated` sites on these paths unreachable. |
| `Execution.lean` | `buy_shares` / `sell_shares` (glass sweep) and `compute_buy_cost` / `compute_sell_cost` return `min(exact greedy cost, u64::MAX)` and leave exactly the greedy spec's remaining levels, for any quantities (only `u64` ranges assumed). `leafSums_spec` proves the fixed `leaf_sums` (SIMD pass exact below 2^52, `u128` fallback, `None` past `u64`). `fixed_*` are regression theorems; the `Legacy` namespace keeps the pre-fix wrapping code and its counterexamples. `sweep_partial_fills` proves the partial-leaf walk never runs out of set bits, so the crate's `invariant_violated` there is unreachable. |
| `HashTable.lean` | `ht_lookup`'s tri-state answer is sound (a found leaf has the key; `ABSENT` is authoritative; `UNKNOWN` only for chains > 5); `find_leaf` is exact; `ht_insert` / `ht_remove` preserve the doubly-linked chain structure. |
| `Bits.lean` | Each intrinsic arm (TZCNT, LZCNT, BLSR, BZHI, PDEP select, POPCNT, from the Intel SDM) equals its portable fallback, and each fallback meets its spec; key layout (`base \| slot = base + slot`, trie-path order = key order, `glass_find_kth_key` reassembly). The Rust now uses only the portable arm for `tz64`/`high_bit`/`clear_lowest_bit`/`find_prev_set_bit` and `count_ones` (the dispatched intrinsics were out-of-line calls), so the portable-arm specs are what apply; PDEP select (TZCNT(PDEP)) and POPCNT run inside the `glass_find_kth_key` kernel on CPUs with hardware PDEP, where the arm-equivalence theorems apply. Line citations in this file refer to the pre-change source. |

## Finding (fixed): leaf-sum overflow

The proofs first required that each leaf's sums fit in `u64`, which nothing
enforced: `leaf_sums` wrapped, and the whole-leaf fast path was then taken
wrongly. Reproduced on the crate before the fix:

| Call | Correct | glass-rs before the fix |
|---|---|---|
| buy 10 from `{10:5, 64:2^63, 65:2^63}` | 370 | 9223372036854775858, book emptied |
| sell 10 into `{10:2^63, 11:2^63, 100:5}` | 555 | 9223372036854776308, book emptied |
| `buy_shares(2^59)` on `{63:2^59}` | `u64::MAX` | 17870283321406128128 |

`leaf_sums` now returns exact totals or `None`; `Execution.lean` proves the
fixed code without the precondition, and `tests/differential.rs` has the
regressions.

## What is *not* proved (assumptions)

* **Model ↔ code.** The proofs are about Lean transcriptions, not the compiled
  Rust; `tests/differential.rs` is what ties the crate to the same spec.
* **The arena trie itself** (internal nodes, ancestor `count`s, masks, the
  linked leaf list pointers, the cached path) is assumed to implement an ordered
  map: `Tiers` treats it as one, `Execution` as a sorted list of leaves with
  `mask` derived from `values`, `HashTable` treats `trie_find_leaf` as exact.
* `leaf_sums_avx512` / `leaf_sums_avx2` are not modeled (the scalar pass is; `test_leaf_sums_paths_agree` checks the SIMD kernels against it).
* Not covered: `iter`/`range`/`top_levels`, `retain`, `split_off`,
  `remove_by_index`, and the tier-level `buy_shares`/`sell_shares` loop around
  `restructure`.
