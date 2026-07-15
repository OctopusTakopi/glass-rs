# Glass — Ordered Set Data Structure for Client-Side Order Books (Rust)

A Rust implementation of the **glass** data structure from the paper
["glass: ordered set data structure for client-side order books"](https://arxiv.org/abs/2506.13991)
by Viktor Krapivensky, with inspiration from the reference C implementation at
[shdown/glass-paper](https://github.com/shdown/glass-paper).

Glass is a trie-based ordered map from `u32` prices to `u64` quantities,
optimized for the access patterns of market data: *sequential locality* (events
cluster near the last touched price) and *edge locality* (events cluster near
the best price). It supports `insert`, `remove`, `get`, `update_value`, `min`,
`max`, `remove_by_index`, and order-book-specific operations `buy_shares`
(market-order execution) and `compute_buy_cost` (cost estimation).

## Why Glass is Fast

1. **Digital search (radix trie)** — key bits are array indices: a fixed,
   shallow 6-level trie (6 bits per level, 36-bit padded key space) with no
   comparison-driven branching.
2. **Cached path** — the traversal path to the last accessed key is memoized.
   A new key resumes from the deepest shared ancestor (paper §5.1), making
   sequential operations effectively O(1).
3. **Bounded cache table (paper §5.2)** — an intrusive hash table embedded in
   the leaf nodes maps partial keys to leaves with a hard O(1) probe bound.
   The probe is *tri-state*: found / definitively absent / "don't know", and
   the rare "don't know" (chain longer than 5) falls back to a trie descent,
   so lookups are both bounded *and* exact.
4. **Linked leaf list** — leaves form a doubly-linked list: O(1) successor and
   predecessor at the leaf level.
5. **Whole-leaf consumption** — `buy_shares` and `compute_buy_cost` process 64
   price levels at a time: one vectorized sum plus one ancestor walk per leaf,
   instead of per-level tree operations.
6. **Hardware acceleration** — BMI1/BMI2/LZCNT bit scans, and AVX-512F/DQ
   (`vpmullq`) leaf reductions where available. All CPU features are detected
   at runtime with portable fallbacks.
7. **Preemption principle (paper §4.5)** — the trie holds only the best
   `MAX_SIZE` (4096) price levels; worse levels overflow into a hash map and
   are pulled back by `restructure()` as the trie drains. This bounds memory
   and keeps the hot book compact in cache.

## Correctness

The two-tier design maintains a strict invariant: every trie key is below the
preemption threshold, which always equals the minimum preempted key and is
updated eagerly on every preemption (as required by paper §4.5). The cache
table implements the paper's tri-state probe semantics exactly.

The test suite includes a 200,000-operation randomized differential test
against `BTreeMap` (deterministic seed) plus targeted regression tests for
historical bugs: hash-chain overflow with colliding keys, stale thresholds
after eviction, zero-value handling in `update_value`, and boundary keys
`0` / `u32::MAX`. Run it with:

```bash
cargo test                     # unit + differential tests
cargo test --release           # exercises the AVX-512 paths under optimization
```

### Semantics worth knowing

- A value of `0` means "absent": `insert(key, 0)` deletes the level, and an
  `update_value` that reaches 0 removes the level (the paper's `adjust`).
- Cost arithmetic (`buy_shares`, `compute_buy_cost`) is saturating.
- The structure is single-threaded by design (`Send` but not `Sync`): reads
  mutate internal caches through interior mutability.
- Key `u32::MAX` (the threshold's saturation point, the paper's "∞") is fully
  supported but always lives in the overflow tier.

## Usage

```rust
use glass_rs::Glass;

fn main() {
    let mut glass = Glass::new();

    // Insert price levels (price -> quantity)
    glass.insert(100, 500);
    glass.insert(110, 300);
    glass.insert(90, 400);

    assert_eq!(glass.get(100), Some(500));
    assert_eq!(glass.min(), Some((90, 400)));
    assert_eq!(glass.max(), Some((110, 300)));

    // Estimate, then execute a market order for 700 shares
    let est = glass.compute_buy_cost(700);
    let cost = glass.buy_shares(700);
    assert_eq!(est, cost); // 90*400 + 100*300
    assert_eq!(glass.get(90), None); // level consumed
}
```

## Configuration

Constants at the top of `src/lib.rs`:

- `BITS_PER_LEVEL` (6): radix width. Not freely tunable — masks and shifts
  assume 6.
- `MAX_SIZE` (4096): trie capacity before preemption kicks in.
- `HT_SIZE` (4096) / `HT_MAX_LOOKUP_LEN` (5): cache-table geometry (paper's J).
- `ARENA_CAPACITY` / `LEAF_ARENA_CAPACITY`: initial node pre-allocation.

## Benchmarks

Run on an **Intel Xeon Gold 6230 @ 2.10GHz** (Cascade Lake: AVX-512F/DQ, BMI2)
with `cargo bench`. Bulk operations perform 1,000,000 operations against a book
of ~1,500 price levels with sequential/local keys; nanoseconds per operation.
Absolute numbers vary with machine load — the glass/BTreeMap ratio within a
run is the stable signal.

| Operation                        | Glass (ns/op) | BTreeMap (ns/op) | Speedup   |
|----------------------------------|---------------|------------------|-----------|
| Insert                           | 5.88          | 51.98            | 8.8x      |
| Get (existing)                   | 2.66          | 51.27            | 19.3x     |
| Get (non-existing)               | 2.70          | 52.66            | 19.5x     |
| Remove (incl. insert)*           | 8.60          | 56.67            | 6.6x      |
| Min                              | 2.23          | 2.53             | 1.1x      |
| Max                              | 3.26          | 3.44             | 1.1x      |
| Compute Buy Cost (1k shares)     | 8.33          | 7.79             | ~parity   |
| **Buy Shares (1k shares)**       | **621**       | **9,558**        | **15.4x** |
| **Compute Buy Cost (500k, deep)**| **250**       | **2,436**        | **9.7x**  |
| **Buy Shares (500k, deep)**      | **2,654**     | **42,892**       | **16.2x** |

\* The remove benchmark re-inserts 1M keys per iteration; remove alone is
≈2.7 ns/op after subtracting the insert cost.

The *deep sweep* benchmarks execute/estimate a 500,000-share order spanning
~24 leaves (≈1,500 price levels), which is where whole-leaf vectorized
consumption dominates per-level tree walks.

## Reference

> glass: ordered set data structure for client-side order books
> Viktor Krapivensky, 2025
> [arXiv:2506.13991](https://arxiv.org/abs/2506.13991)

> https://github.com/shdown/glass-paper

## License

Dual-licensed under MIT and CC-BY-4.0.
