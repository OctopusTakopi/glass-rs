# Glass - Ordered Set Data Structure for Client-Side Order Books (Rust Implementation)

This repository contains a Rust implementation of the "glass" data structure, as described in the paper ["glass: ordered set data structure for client-side order books"](https://arxiv.org/abs/2506.13991) by Viktor Krapivensky. The glass structure is a trie-based ordered set optimized for integer keys and sequential locality, particularly suited for managing client-side order books in market data applications. It supports operations like insert, erase, find, min, max, and order book-specific features such as computing buy costs and removing by index.

The implementation draws inspiration from the original C code in the [shdown/glass-paper](https://github.com/shdown/glass-paper) repository but is adapted for Rust, leveraging features like cell-based interior mutability, x86 intrinsics, and the `ahash` crate for efficient hashing.

## WARN

WARN: This repo is currently in a runnable state and is also just a proof of concept. The performance and correctness are not yet at a production level. The original C implementation can achieve an average of 6ns for insert, remove, and find operations on my local machine, but C version performs similarly as this implementation at around 16ns on a c7i-flex.large instance. I don't know why, maybe it's because of the L1 cache size?

## Key Features

- **Trie-based Structure**: A radix trie with configurable bits per level (default: 6 bits, 64 children per node) for efficient storage and traversal of 32-bit integer keys.
- **Cached Path**: Exploits sequential locality for faster traversals, with fast truncation during erase operations.
- **Hash Table Cache**: Uses a `HashMap` (via `ahash`) for O(1) lookups to pre-leaf nodes.
- **Hardware Acceleration**: Utilizes x86-64 BMI1, BMI2, and LZCNT intrinsics for bit operations like finding next/previous set bits, if available on the hardware.
- **Preemption and Restructure**: Maintains a maximum size (default: 4096 elements) by preempting elements to a separate `HashMap` when exceeding limits, with a restructure operation to balance memory usage.
- **Order Book Optimizations**: Supports computing the cost of buying shares (e.g., for market orders) and removing elements by their order in the sorted set.
- **Count Tracking**: Each node tracks the subtree size for efficient k-th element finding and min/max operations.
- **Thread Safety**: Uses `Cell` and `UnsafeCell` for interior mutability; note that the structure is not thread-safe by default.
- **Benchmarked Performance**: Shows significant speedups over Rust's `BTreeMap` in various operations (see Benchmarks section below).

## Technologies Used

- **Rust**: Core language (version 1.60+ recommended for feature detection and intrinsics).
- **Crates**:
  - `ahash`: For fast, non-cryptographic hashing in `HashMap`.
  - `std::arch::x86_64`: For CPU feature detection and intrinsics (BMI1, BMI2, LZCNT).
- **Optional Hardware**: x86-64 architecture with BMI2 support for optimal performance.

If you encounter errors:
- **"undefined symbol: _tzcnt_u64" or similar**: Ensure your CPU supports the required intrinsics or compile without native flags. The code falls back to software bit operations.
- **Build failures on non-x86**: The code is x86-specific;

## Usage Examples

The `Glass` struct provides an API for ordered set operations, optimized for order books where keys are prices (u32) and values are quantities (u64).

```rust
use glass::Glass;

fn main() {
    let mut glass = Glass::new();

    // Insert key-value pairs (price: quantity)
    glass.insert(100, 500); // Insert 500 shares at price 100
    glass.insert(110, 300);
    glass.insert(90, 400);

    // Get a value
    if let Some(quantity) = glass.get(100) {
        println!("Quantity at 100: {}", quantity); // 500
    }

    // Update a value
    glass.update_value(100, |q| *q += 100); // Now 600 at 100

    // Remove by key
    glass.remove(110);

    // Get min and max
    println!("Min: {:?}", glass.min()); // Some((90, 400))
    println!("Max: {:?}", glass.max()); // Some((100, 600))

    // Compute cost to buy 700 shares (processes from lowest price)
    let cost = glass.compute_buy_cost(700);
    println!("Cost: {}", cost); // (90 * 400) + (100 * 300) = 36000 + 30000 = 66000

    // Buy shares (modifies the structure)
    let total_cost = glass.buy_shares(500);
    println!("Buy cost: {}", total_cost); // Buys from min prices, removes if depleted

    // Remove by index (0-based in sorted order)
    glass.remove_by_index(0); // Removes the smallest remaining element
}
```

## Configuration

Configuration is done via constants at the top of the source file:
- `BITS_PER_LEVEL: usize = 6;`: Bits per trie level (power of 2, affects child count: 64).
- `KEY_BITS: usize = 32;`: Bit width of keys (u32).
- `MAX_SIZE: usize = 4096;`: Maximum elements in the glass before preemption.
- `ARENA_CAPACITY: usize = 16384;`: Initial capacity for node arena.

To customize:
- Edit these constants and rebuild.
- No config files; all hardcoded right now.

If using preemption, the threshold (`thres`) is dynamically managed, but you can access fields like `glass.thres.get()`.

## Benchmarks

Benchmarks were run on a c7i-flex.large with Intel(R) Xeon(R) Platinum 8488C (2) @ 2.40 GHz CPU machine, structure with 1,000,000 elements. Times are normalized to nanoseconds per operation (dividing total ms by 1M for bulk operations; µs/ms converted to ns for single ops like remove_by_index).

| Operation              | Glass (ns/op) | BTreeMap (ns/op) | Speedup (Glass faster by) |
|------------------------|---------------|------------------|---------------------------|
| Insert                | 13.68        | 51.43           | 3.76x                    |
| Get Existing          | 6.83         | 49.17           | 7.20x                    |
| Get Non-Existing      | 6.79         | 48.83           | 7.19x                    |
| Remove                | 15.84        | 53.21           | 3.36x                    |
| Min                   | 2.38         | 5.16            | 2.17x                    |
| Max                   | 1.89         | 5.36            | 2.84x                    |
| Compute Buy Cost      | 40.12        | 6.72            | 0.17x (BTree faster)     |
| Remove by Index (Start) | 99108      | 50169           | 0.51x (BTree faster)     |
| Remove by Index (End) | 248310       | 1718200         | 6.92x                    |
| Remove by Index (Random) | 262130    | 1044500         | 3.98x                    |

Note: Changes from previous benchmarks indicate improvements in most operations. Compute buy cost and remove from start favor BTreeMap, but glass excels in lookups and removes from end/random. (not optimized yet)

## Reference

> glass: ordered set data structure for client-side order books
> Viktor Krapivensky
> year 2025
> eprint 2506.13991
> archivePrefix arXiv
> primaryClass cs.DS
> url https://arxiv.org/abs/2506.13991

> https://github.com/shdown/glass-paper

## License

This project is dual-licensed under:
- [CC-BY-4.0](LICENSE.CC-BY-4.0): For the paper and documentation.
- [MIT](LICENSE.MIT): For the code.
