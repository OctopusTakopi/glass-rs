# Glass - Ordered Set Data Structure for Client-Side Order Books (Rust Implementation)

This repository contains a Rust implementation of the "glass" data structure, as described in the paper ["glass: ordered set data structure for client-side order books"](https://arxiv.org/abs/2506.13991) by Viktor Krapivensky. The glass structure is a trie-based ordered set optimized for integer keys and sequential locality, particularly suited for managing client-side order books in market data applications. It supports operations like insert, erase, find, min, max, and order book-specific features such as computing buy costs and removing by index.

The implementation draws inspiration from the original C code in the [shdown/glass-paper](https://github.com/shdown/glass-paper) repository but is adapted for Rust, leveraging features like cell-based interior mutability, x86 intrinsics, and a custom intrusive hash table.

## Why Glass is Fast

Glass achieves significant speedups (up to **24x over BTreeMap**) by optimizing for the specific access patterns of market data:

1.  **Digital Search (Radix Trie)**: Unlike B-Trees which use comparison-based logic ($O(\log N)$ branches), Glass uses the bits of the key as array indices. This results in a fixed, shallow depth (6 levels for 32-bit keys) and eliminates expensive comparison-driven branching.
2.  **Sequential Locality (Cached Path)**: Market events usually occur near the "best" price or the last processed price. Glass caches the traversal path to the last accessed key. If the next key shares a prefix (high `lambda`), Glass jumps directly to the shared ancestor, making sequential operations effectively $O(1)$.
3.  **Intrusive Bounded Hash Table**: For point lookups, Glass uses an intrusive hash table embedded directly in the leaf nodes. This provides a hard-bounded $O(1)$ lookup to the "pre-leaf" level, bypassing trie traversal entirely for frequently accessed price levels.
4.  **Linked Leaf List**: Leaf nodes are organized in a doubly-linked list. This allows **O(1) transitions** to the next or previous price level. This is why market order execution (`buy_shares`) is exponentially faster than B-Trees, which must traverse tree levels to find successors.
5.  **Hardware Acceleration**: Glass leverages x86-64 bit manipulation instructions (BMI1, BMI2, LZCNT). Instructions like `_tzcnt_u64` and `_bzhi_u64` allow scanning 64 price levels in a single CPU cycle to find the next available quote.
6.  **Dual-Arena Density**: By using separate arenas for Internal and Leaf nodes, Glass packs up to 64 sequential price levels into a single contiguous `LeafNode`, maximizing L1/L2 cache efficiency.

## WARN

WARN: This implementation is a high-performance refactor optimized for **Intel(R) Xeon(R) Gold 6230** architecture. It is significantly faster than the initial proof-of-concept but remains a specialized tool for single-threaded market data processing.

## Key Features

- **Trie-based Structure**: A radix trie with 6 bits per level (64 children per node) for efficient storage and traversal of 32-bit integer keys.
- **Linked Leaf List**: O(1) successor/predecessor access for fast market order aggregation.
- **Cached Path**: Exploits sequential locality for faster traversals.
- **Bounded HT Cache**: Hard O(1) lookups to pre-leaf nodes via intrusive chaining.
- **Hardware Acceleration**: Utilizes x86-64 BMI1, BMI2, and LZCNT intrinsics.
- **Preemption and Restructure**: Maintains a maximum glass size (default: 4096) to keep the "hot" portion of the book in the fast trie.
- **Order Book Optimizations**: Fast `buy_shares` (market order) and `compute_buy_cost` (estimation) logic.

## Technologies Used

- **Rust**: Core language (version 1.60+ for intrinsics).
- **Crates**:
  - `ahash`: Used for internal hash distributions.
  - `std::arch::x86_64`: For CPU feature detection and intrinsics (BMI1, BMI2, LZCNT).
- **Hardware**: Best performance achieved on x86-64 with BMI2 support.

## Usage Examples

```rust
use glass_rs::Glass;

fn main() {
    let mut glass = Glass::new();

    // Insert key-value pairs (price: quantity)
    glass.insert(100, 500); 
    glass.insert(110, 300);
    glass.insert(90, 400);

    // Get a value
    if let Some(quantity) = glass.get(100) {
        println!("Quantity at 100: {}", quantity);
    }

    // Execute buy order (modifies book, deletes depleted levels)
    let total_cost = glass.buy_shares(700);
    println!("Buy cost: {}", total_cost);

    // Get min and max
    println!("Min: {:?}", glass.min());
}
```

## Configuration

Constants at the top of `src/lib.rs`:
- `BITS_PER_LEVEL`: 6 (Power of 2, radix size).
- `MAX_SIZE`: 4096 (Trie capacity before preemption).
- `ARENA_CAPACITY`: Initial node allocation.

## Benchmarks

Benchmarks were run on an **Intel(R) Xeon(R) Gold 6230 CPU @ 2.10GHz**. Bulk operations performed 1,000,000 operations on a set with sequential/local keys.

| Operation              | Glass (ns/op) | BTreeMap (ns/op) | Speedup (Glass faster by) |
|------------------------|---------------|------------------|---------------------------|
| Insert                | 11.11         | 97.44           | 8.77x                    |
| Get Existing          | 5.76          | 86.94           | 15.09x                   |
| Get Non-Existing      | 5.77          | 86.99           | 15.07x                   |
| Remove (Inc. Insert)  | 14.11         | 98.90           | 7.01x                    |
| Min                   | 6.24          | 5.23            | 0.84x (BTree faster)     |
| Max                   | 4.39          | 6.24            | 1.42x                    |
| **Compute Buy Cost**  | **17.62**     | **14.92**       | **~0.8x (Parity)**       |
| **Buy Shares (Market)**| **740.09**    | **18108.00**    | **24.47x**               |
| Remove by Index (Start)| 110680        | 107690          | 0.97x (Parity)           |
| Remove by Index (End)  | 573260        | 4826100         | 8.42x                    |
| Remove by Index (Random)| 402600       | 2671400         | 6.63x                    |

## Reference

> glass: ordered set data structure for client-side order books
> Viktor Krapivensky, 2025
> [arXiv:2506.13991](https://arxiv.org/abs/2506.13991)

> https://github.com/shdown/glass-paper

## License

Dual-licensed under MIT and CC-BY-4.0.
