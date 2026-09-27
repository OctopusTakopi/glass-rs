# Glass — Ordered Set Data Structure for Client-Side Order Books (Rust)

Rust port of **glass** ([arXiv:2506.13991](https://arxiv.org/abs/2506.13991), Viktor Krapivensky; reference C at [shdown/glass-paper](https://github.com/shdown/glass-paper)): a trie-based ordered map from `u32` prices to `u64` quantities, built for client-side order books. It exploits the two localities of market data (events cluster near the last touched price and near the best price) and adds order-book primitives like market-order execution on top of a `BTreeMap`-style API.

## Benchmarks

Intel Xeon Gold 6230 @ 2.10GHz (running at 2.8 GHz), tuned profile `latency-performance`, `nightly-2026-09-25`, JCC mitigation flag on (which also speeds up the BTreeMap baseline, so the ratios are honest). Pinned to an idle core with an idle SMT sibling; best median of two full `cargo bench` runs (they agreed within a few percent). Bulk benches do 1M ops against a book of 1,500 price levels (random keys in 500..2000, random quantities 1..1000, fixed seeds).

| Operation                           | Glass (ns/op) | BTreeMap (ns/op) | Speedup   |
|-------------------------------------|---------------|------------------|-----------|
| Insert                              | 4.32          | 65.6             | 15.2x     |
| Get (existing)                      | 3.26          | 65.7             | 20.2x     |
| Get (non-existing)                  | 3.26          | 65.7             | 20.2x     |
| Remove (incl. insert)*              | 5.82          | 66.3             | 11.4x     |
| Min                                 | 2.80          | 3.43             | 1.2x      |
| Max                                 | 3.09          | 4.51             | 1.5x      |
| **Top 25 Levels (snapshot)**        | **42.1**      | **62.4**         | **1.5x**  |
| Compute Buy Cost (1k shares)        | 7.60          | 8.83             | 1.2x      |
| Compute Sell Cost (1k shares)       | 10.8          | 13.4             | 1.2x      |
| Buy Shares (1k shares)              | 412           | 431              | ~parity   |
| Sell Shares (1k shares)             | 372           | 938              | 2.5x      |
| Compute Buy Cost (500k, deep)       | 434           | 2,703            | 6.2x      |
| Compute Sell Cost (500k, deep)      | 544           | 2,628            | 4.8x      |
| **Buy Shares (500k, deep)**         | **2,752**     | **48,696**       | **17.7x** |
| **Sell Shares (500k, deep)**        | **2,701**     | **80,517**       | **29.8x** |
| Remove by Index (min, drain)        | 45.5          | 54.0             | 1.2x      |
| **Remove by Index (max, drain)**    | **93.2**      | **1,478**        | **15.9x** |
| **Remove by Index (random, drain)** | **95.0**      | **898**          | **9.5x**  |

\* The remove bench re-inserts 1M keys per iteration; remove alone is ≈1.5 ns/op after subtracting the insert.

The *deep* rows execute/estimate a 500k-share order spanning ≈1,000 levels (~16 of the book's 24 leaves), where whole-leaf vectorized consumption beats per-level tree walks. The 1k-share rows touch ~2 levels of a book whose setup just streamed 12 MB of keys and values, so they mostly measure a handful of cache misses, and glass and `BTreeMap` land close together. *Remove by Index* drains the whole book by rank (1,500 removals per iteration). Absolute numbers vary with machine load and turbo; the glass/BTreeMap ratio within a run is the stable signal.

Earlier versions of this table timed dropping the whole book inside the setup-based benches (buy/sell shares, remove by index), which mostly inflated the `BTreeMap` side: its 1k-share buy went from 12.9 µs to 0.43 µs once the drop moved out of the timed region.

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
- **Hardware acceleration**: AVX-512F/DQ leaf reductions, with an AVX2 build of the same reduction for CPUs without AVX-512 and a scalar fallback; PDEP k-th-bit select. All runtime-detected; builds on any architecture (aarch64 is checked). Bit scans are plain `trailing_zeros`/`leading_zeros`, which inline to `bsf`/`bsr`: a runtime-dispatched BMI intrinsic cannot inline into a baseline-x86-64 caller and costs a call per scan.
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
- Cost arithmetic saturates instead of overflowing, and the result is exact: `min(true cost, u64::MAX)`, including books whose quantities sum past `u64` within one 64-price leaf.
- Requires a nightly toolchain (pinned in `rust-toolchain.toml`): it uses `core::hint::{likely, unlikely}` and the portable `core::hint::prefetch_*`.
- Library code has no bare `unwrap`/`expect`. A state the internal invariants rule out (a bug, or memory corruption) panics in every build with a message naming the invariant, rather than returning plausible wrong prices.
- `Send` but not `Sync` (its caches are `Cell`s): move it between threads, don't share it.
- `u32::MAX` is a valid key (the paper's "∞") but always sits in the overflow tier.
- Only the lowest prices live in the fast trie: up to 4096, refilled from the overflow tier once it is 32 levels short. If you keep a deep bid book and mostly sell, store negated prices (`!price`) and use the buy-side ops.

Tested with a 200k-operation randomized differential test against `BTreeMap` (fixed seed), randomized market-order sequences on market-shaped and scattered books, an exact `u128` oracle over huge quantities, and regression tests for past bugs. `cargo test`, and `cargo test --release` to cover the AVX-512 paths; `cargo test --features check-invariants` adds a full structural self-check (`Glass::check_invariants`) through the randomized tests. `fuzz/` holds a coverage-guided fuzz target (cargo-fuzz) that checks every operation against a `BTreeMap` oracle and every internal invariant after each step.

Docs: `cargo doc --open`, example in `examples/demo.rs`. [`demos/binance-tui`](demos/binance-tui) runs a live Binance USDT-M perpetual book in a `BTreeMap` book and a glass-rs book side by side, cross-checking them on every update.

## Tuning

**JCC erratum (Skylake-SP / Cascade Lake):** `.cargo/config.toml` sets `-C llvm-args=-x86-branches-within-32B-boundaries`. On affected CPUs, branches touching a 32-byte boundary disable the uop cache for their line; we measured layout-dependent swings up to ~80% between identical builds. The flag pads branches, making hot paths faster *and* stable. Cargo config does not propagate to dependents, so set the flag in your own build when deploying to affected CPUs.

Constants at the top of `src/lib.rs`: `MAX_SIZE` (4096, trie capacity before preemption), `HT_SIZE`/`HT_MAX_LOOKUP_LEN` (cache-table geometry, paper's J), `ARENA_CAPACITY`/`LEAF_ARENA_CAPACITY` (pre-allocation). `BITS_PER_LEVEL` is not freely tunable; masks and shifts assume 6.

Going further:

- `-C target-cpu=native` (or `+bmi1,+bmi2,+lzcnt,+popcnt`) turns the bit scans into `tzcnt`/`lzcnt`/`blsr`/`popcnt`; measured within ~3% of the portable build.
- PGO (`cargo-pgo`) with a recording of your feed; `-Z build-std` extends flags to std.
- Deployment: pin the thread + `performance` governor, THP (`madvise`) for the multi-MB arenas, L3 partitioning (resctrl) to protect the hot trie from noisy neighbors.

## Reference

> glass: ordered set data structure for client-side order books
> Viktor Krapivensky, 2025
> [arXiv:2506.13991](https://arxiv.org/abs/2506.13991)

> https://github.com/shdown/glass-paper

## License

Dual-licensed under MIT and CC-BY-4.0.
