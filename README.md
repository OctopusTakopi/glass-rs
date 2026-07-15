# Glass — Ordered Set Data Structure for Client-Side Order Books (Rust)

Rust port of **glass** ([arXiv:2506.13991](https://arxiv.org/abs/2506.13991), Viktor Krapivensky; reference C at [shdown/glass-paper](https://github.com/shdown/glass-paper)): a trie-based ordered map from `u32` prices to `u64` quantities, built for client-side order books. It exploits the two localities of market data (events cluster near the last touched price and near the best price) and adds order-book primitives like market-order execution on top of a `BTreeMap`-style API.

## Benchmarks

Intel Xeon Gold 6230 @ 2.10GHz, `cargo bench`, single run pinned to an idle core, JCC mitigation flag on (which also speeds up the BTreeMap baseline, so the ratios are honest). Bulk benches do 1M ops against a book of ~1,500 price levels with sequential/local keys.

| Operation                         | Glass (ns/op) | BTreeMap (ns/op) | Speedup   |
|-----------------------------------|---------------|------------------|-----------|
| Insert                            | 4.09          | 50.41            | 12.3x     |
| Get (existing)                    | 2.40          | 43.83            | 18.3x     |
| Get (non-existing)                | 2.36          | 43.85            | 18.6x     |
| Remove (incl. insert)*            | 5.02          | 51.07            | 10.2x     |
| Min                               | 2.88          | 2.48             | 0.9x      |
| Max                               | 3.68          | 3.16             | 0.9x      |
| **Top 25 Levels (snapshot)**      | **29.8**      | **46.5**         | **1.6x**  |
| Compute Buy Cost (1k shares)      | 8.16          | 6.30             | 0.8x      |
| Compute Sell Cost (1k shares)     | 10.34         | 10.55            | ~parity   |
| **Buy Shares (1k shares)**        | **577**       | **9,382**        | **16.3x** |
| **Sell Shares (1k shares)**       | **703**       | **9,606**        | **13.7x** |
| Compute Buy Cost (500k, deep)     | 358           | 2,006            | 5.6x      |
| Compute Sell Cost (500k, deep)    | 334           | 2,037            | 6.1x      |
| **Buy Shares (500k, deep)**       | **2,519**     | **31,063**       | **12.3x** |
| **Sell Shares (500k, deep)**      | **2,519**     | **59,868**       | **23.8x** |

\* The remove bench re-inserts 1M keys per iteration; remove alone is ≈0.9 ns/op after subtracting the insert.

The *deep* rows execute/estimate a 500k-share order spanning ~24 leaves (≈1,500 levels), where whole-leaf vectorized consumption beats per-level tree walks. Absolute numbers vary with machine load; the glass/BTreeMap ratio within a run is the stable signal.

## Usage

```rust
use glass_rs::Glass;

fn main() {
    let mut book = Glass::new();

    // Insert price levels (price -> quantity)
    book.insert(100, 500);
    book.insert(110, 300);
    book.insert(90, 400);

    assert_eq!(book.get(100), Some(500));
    assert_eq!(book.min(), Some((90, 400)));
    assert_eq!(book.max(), Some((110, 300)));
    assert_eq!(book.len(), 3);

    // Iterate levels in ascending price order (top of book first)
    for (price, qty) in book.iter().take(25) {
        println!("{price} x {qty}");
    }

    // Estimate, then execute a market order for 700 shares
    let est = book.compute_buy_cost(700);
    let cost = book.buy_shares(700);
    assert_eq!(est, cost); // 90*400 + 100*300
    assert_eq!(book.get(90), None); // level consumed
}
```

## Why it's fast

- **Radix trie**: key bits are array indices. A fixed 6-level trie (6 bits/level), no comparison branching.
- **Cached path**: the traversal to the last touched key is memoized; the next key resumes from the deepest shared ancestor (paper §5.1). Sequential access is effectively O(1).
- **Bounded cache table** (paper §5.2): an intrusive hash table embedded in the leaves, hard 5-probe bound. Tri-state result (found / absent / don't-know); the rare don't-know falls back to a trie descent, so lookups are bounded *and* exact.
- **Linked leaf list**: O(1) successor/predecessor across leaves.
- **Whole-leaf consumption**: `buy_shares`/`compute_buy_cost` process 64 price levels at a time, one vectorized sum + one ancestor walk per leaf.
- **Hardware acceleration**: BMI1/BMI2/LZCNT/POPCNT bit scans, AVX-512F/DQ leaf reductions. All runtime-detected with portable fallbacks; builds on any architecture (CI checks aarch64).
- **Preemption** (paper §4.5): the trie holds only the best 4096 levels; worse levels overflow to a hash map and come back as the trie drains. The hot book stays compact in cache.

## API

The map API follows `std::collections::BTreeMap`: `get`, `get_key_value`, `contains_key`, `insert`, `remove`, `len`, `is_empty`, `clear`, `iter`, `keys`, `values`, `range`, `first_key_value`, `last_key_value`, `pop_first`, `pop_last`, `retain`, `split_off`, `Extend`/`FromIterator`/`IntoIterator`, `Debug`.

On top of that:

- `buy_shares` / `compute_buy_cost`: execute or estimate a market order from the lowest price up (ask book).
- `sell_shares` / `compute_sell_cost`: same from the highest price down (bid book).
- `top_levels(n, &mut buf)`: snapshot of the best `n` levels into your own buffer, no allocation in steady state.
- `next_level` / `prev_level`: successor and predecessor level.
- `remove_by_index`: remove the k-th smallest level.

Things to know:

- Quantity 0 means the level doesn't exist: `insert(key, 0)` deletes, and an `update_value` that hits 0 removes the level. This is also why there is no `get_mut`/`entry` (writing 0 through a raw `&mut u64` would corrupt the structure); use `update_value`.
- Cost arithmetic saturates instead of overflowing.
- Single-threaded (`Send` but not `Sync`); reads update internal caches.
- `u32::MAX` is a valid key (the paper's "∞") but always sits in the overflow tier.
- Only the lowest 4096 prices live in the fast trie. If you keep a deep bid book and mostly sell, store negated prices (`!price`) and use the buy-side ops.

Tested with a 200k-operation randomized differential test against `BTreeMap` (fixed seed) plus regression tests for past bugs. `cargo test`, and `cargo test --release` to cover the AVX-512 paths.

Docs: `cargo doc --open`, example in `examples/demo.rs`.

## Tuning

**JCC erratum (Skylake-SP / Cascade Lake):** `.cargo/config.toml` sets `-C llvm-args=-x86-branches-within-32B-boundaries`. On affected CPUs, branches touching a 32-byte boundary disable the uop cache for their line; we measured layout-dependent swings up to ~80% between identical builds. The flag pads branches, making hot paths faster *and* stable. Cargo config does not propagate to dependents, so set the flag in your own build when deploying to affected CPUs.

Constants at the top of `src/lib.rs`: `MAX_SIZE` (4096, trie capacity before preemption), `HT_SIZE`/`HT_MAX_LOOKUP_LEN` (cache-table geometry, paper's J), `ARENA_CAPACITY`/`LEAF_ARENA_CAPACITY` (pre-allocation). `BITS_PER_LEVEL` is not freely tunable; masks and shifts assume 6.

Going further:

- `--features nightly`: `likely`/`unlikely` hints on hot branches (no-op on stable).
- PGO (`cargo-pgo`) with a recording of your feed; `-Z build-std` extends flags to std.
- Deployment: pin the thread + `performance` governor, THP (`madvise`) for the multi-MB arenas, L3 partitioning (resctrl) to protect the hot trie from noisy neighbors.

## Reference

> glass: ordered set data structure for client-side order books
> Viktor Krapivensky, 2025
> [arXiv:2506.13991](https://arxiv.org/abs/2506.13991)

> https://github.com/shdown/glass-paper

## License

Dual-licensed under MIT and CC-BY-4.0.
