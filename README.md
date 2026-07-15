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
6. **Hardware acceleration** — BMI1/BMI2/LZCNT/POPCNT bit scans, and
   AVX-512F/DQ (`vpmullq`) leaf reductions where available. All CPU features
   are detected at runtime with portable fallbacks; the crate builds on any
   architecture (CI checks aarch64).
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

### API surface

The map API mirrors `std::collections::BTreeMap` where it makes sense:
`get`, `get_key_value`, `contains_key`, `insert`, `remove`, `len`,
`is_empty`, `clear`, `iter`, `keys`, `values`, `range`, `first_key_value`,
`last_key_value`, `pop_first`, `pop_last`, `retain`, `split_off`,
`Extend`/`FromIterator`/`IntoIterator` (borrowed and owning), and `Debug`.

Deliberately **not** provided: `get_mut`/`values_mut`/`entry` — a raw
`&mut u64` would let callers write 0 and corrupt the occupancy invariant.
Use `update_value` (closure-based in-place adjust; reaching zero deletes the
level, per the paper's `adjust`).

Order-book operations beyond the map API:

- `buy_shares` / `compute_buy_cost` — market-order execution/estimation from
  the *lowest* price upward (ask book).
- `sell_shares` / `compute_sell_cost` — the mirror: execution/estimation from
  the *highest* price downward (bid book). The overflow tier holds the
  highest prices and is drained first; trie leaves are then consumed whole
  from the max leaf backward with the same vectorized sums.
- `next_level` / `prev_level` — successor/predecessor level (the paper's
  `next`/`prev`), O(1) via the linked leaf list when the neighbor shares a
  leaf.
- `remove_by_index` — k-th smallest level, via per-subtree counts.

Note for deep bid books (> 4096 levels): the preemption tier keeps the
*lowest* prices in the fast trie. If your workload is sell-heavy against a
very deep book, store negated prices (`!price`) and use the buy-side
operations so the best bids stay in the trie.

See `cargo doc --open` and `examples/demo.rs`.

## Build configuration for Skylake/Cascade Lake (JCC erratum)

This repository sets `-C llvm-args=-x86-branches-within-32B-boundaries` in
`.cargo/config.toml`. On CPUs affected by the Intel JCC erratum (Skylake-SP /
Cascade Lake, e.g. Xeon Gold 62xx), conditional branches that touch a 32-byte
code boundary disable the uop cache for their line; in our measurements this
caused layout-dependent swings of up to ~80% on hot loops between otherwise
identical builds. The flag pads branches so this cannot happen and made every
hot path measurably faster and *stable* across rebuilds.

Cargo config does **not** propagate to dependent crates — applications
embedding glass-rs should set the same flag in their own build when deploying
to affected CPUs.

## Deployment tuning (system level)

For latency-critical deployment on a machine like the Xeon Gold 62xx this was
tuned on, the following complement the in-crate optimizations:

- **CPU pinning + `performance` governor** — pin the market-data thread
  (`taskset`/`isolcpus`) and disable frequency scaling; Glass is
  single-threaded by design.
- **Transparent Huge Pages** — the arenas span several MB; 2MB pages cut dTLB
  pressure on random access (`madvise` THP mode is a good default).
- **L3 partitioning (`cat_l3`/resctrl)** — the hot trie is designed to sit in
  cache; dedicating L3 ways to the order-book process protects it from noisy
  neighbors.

Instruction-set notes from tuning on this CPU: hardware `popcnt` dispatch is
worth ~10-15% on `remove_by_index` (rustc does not emit it on the baseline
target); 512-bit leaf reductions beat a 256-bit AVX-512VL variant by ~17% on
deep estimation sweeps (the "heavy license" downclock concern does not apply
to this bursty usage); `buy_shares` prefetches the next leaf with intent to
write (`prefetchw`). `bsf`/`bsr` vs `tzcnt`/`lzcnt` makes no measurable
difference on Intel cores for the non-zero masks used here.

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
| Insert                           | 4.24          | 51.48            | 12.1x     |
| Get (existing)                   | 2.43          | 47.19            | 19.4x     |
| Get (non-existing)               | 2.51          | 47.96            | 19.1x     |
| Remove (incl. insert)*           | 5.13          | 52.65            | 10.3x     |
| Min                              | 2.97          | 2.76             | ~parity   |
| Max                              | 3.79          | 3.22             | ~parity   |
| Compute Buy Cost (1k shares)     | 11.10         | 8.18             | 0.7x      |
| **Buy Shares (1k shares)**       | **773**       | **9,971**        | **12.9x** |
| **Compute Buy Cost (500k, deep)**| **297**       | **2,066**        | **7.0x**  |
| **Buy Shares (500k, deep)**      | **2,495**     | **31,558**       | **12.6x** |
| Compute Sell Cost (1k shares)    | 8.67          | 9.52             | 1.1x      |
| **Sell Shares (1k shares)**      | **595**       | **9,568**        | **16.1x** |
| Compute Sell Cost (500k, deep)   | 290           | 2,087            | 7.2x      |
| **Sell Shares (500k, deep)**     | **2,642**     | **60,611**       | **22.9x** |

\* The remove benchmark re-inserts 1M keys per iteration; remove alone is
≈0.9 ns/op after subtracting the insert cost. All rows built with the JCC
mitigation flag (see below), which also speeds up the BTreeMap baseline —
these ratios are honest.

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
