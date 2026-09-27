//! Seeded random-walk fuzzing: long operation sequences through the same
//! harness as the libFuzzer target (`glass_rs_fuzz::run`: a `BTreeMap`
//! oracle and `check_invariants` after every step), shrinking any failure to
//! a minimal sequence.
//!
//! Coverage-guided fuzzing is weak at deep, state-dependent bugs: the
//! stale-path-cache bug needs a particular 4-operation sequence that adds no
//! new coverage on the way, and libFuzzer never produced it. Long random
//! walks with state-relative keys and sizes hit it within a few dozen seeds.
//!
//! cargo run --release --bin walk -- FIRST_SEED LAST_SEED [OPS_PER_SEED]

use glass_rs_fuzz::{Key, Op, Qty, Size, run};

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    /// Index into `weights`, chosen with probability proportional to each.
    fn pick(&mut self, weights: &[u64]) -> usize {
        let mut r = self.below(weights.iter().sum());
        weights
            .iter()
            .position(|&w| {
                let hit = r < w;
                r = r.saturating_sub(w);
                hit
            })
            .unwrap_or(0)
    }
}

fn key(r: &mut Rng) -> Key {
    match r.pick(&[40, 10, 10, 20, 10, 5, 5]) {
        0 => Key::Near(r.next() as u16, (r.below(9) as i8) - 4),
        1 => Key::Min((r.below(9) as i8) - 4),
        2 => Key::Max((r.below(9) as i8) - 4),
        3 => Key::Sparse(r.next() as u32),
        4 => Key::Dense(r.next() as u16),
        5 => Key::Collide(r.next() as u8, r.next() as u8),
        _ => Key::Edge(r.next() as u8),
    }
}

fn qty(r: &mut Rng) -> Qty {
    match r.pick(&[80, 8, 5, 5, 2]) {
        0 => Qty::Small(1 + r.below(5000) as u16),
        1 => Qty::Raw(r.next()),
        2 => Qty::NearBound(r.below(2) == 0, r.next() as u8),
        3 => Qty::NearMax(r.next() as u16),
        _ => Qty::Zero,
    }
}

fn size(r: &mut Rng) -> Size {
    match r.pick(&[50, 25, 15, 5, 5]) {
        0 => Size::Levels(r.below(8) as u8, (r.below(5) as i8) - 2),
        1 => Size::Small(r.next() as u16),
        2 => Size::Thousands(r.below(100_000) as u32),
        3 => Size::Raw(r.next()),
        _ => Size::All,
    }
}

fn op(r: &mut Rng) -> Op {
    let w = [15, 8, 5, 8, 10, 10, 4, 4, 6, 5, 5, 3, 3, 2, 2, 1, 1, 1, 1];
    match r.pick(&w) {
        0 => Op::Insert(key(r), qty(r)),
        1 => Op::Remove(key(r)),
        2 => Op::Get(key(r)),
        3 => Op::Update(key(r), r.below(4001) as i64 - 2000),
        4 => Op::Buy(size(r)),
        5 => Op::Sell(size(r)),
        6 => Op::BuyCost(size(r)),
        7 => Op::SellCost(size(r)),
        8 => Op::RemoveByIndex(r.next() as u16),
        9 => Op::PopFirst,
        10 => Op::PopLast,
        11 => Op::Next(key(r)),
        12 => Op::Prev(key(r)),
        13 => Op::Range(key(r), key(r)),
        14 => Op::Top(r.next() as u16),
        15 => Op::SplitOff(key(r)),
        16 => Op::Bulk {
            start: key(r),
            stride: r.below(64) as u8,
            count: r.below(2000) as u16,
            qty: qty(r),
        },
        17 => Op::Retain(r.next() as u8),
        _ => Op::Check,
    }
}

/// A starting book and a walk over it. Even seeds start from scattered keys
/// (every leaf alone in its subtree); odd ones from a market-shaped book,
/// dense near the top and sparse in the tail, often past the 4096-level trie
/// capacity.
fn sequence(seed: u64, len: usize) -> Vec<Op> {
    let mut r = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
    let mut ops = Vec::new();
    if seed.is_multiple_of(2) {
        for _ in 0..20 + r.below(300) {
            ops.push(Op::Insert(
                Key::Sparse(r.next() as u32),
                Qty::Small(1 + r.below(5000) as u16),
            ));
        }
    } else {
        let base = Key::Sparse(r.next() as u32 | 0x8000_0000);
        ops.push(Op::Bulk {
            start: base,
            stride: r.below(3) as u8,
            count: 800,
            qty: Qty::Small(1 + r.below(5000) as u16),
        });
        for _ in 0..r.below(6) {
            ops.push(Op::Bulk {
                start: Key::Max(1),
                stride: 20 + r.below(200) as u8,
                count: 1 + r.below(1500) as u16,
                qty: qty(&mut r),
            });
        }
    }
    ops.extend((0..len).map(|_| op(&mut r)));
    ops
}

fn fails(ops: &[Op]) -> Option<String> {
    std::panic::catch_unwind(|| run(ops)).err().map(|e| {
        e.downcast_ref::<String>()
            .cloned()
            .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
            .unwrap_or_default()
    })
}

/// Delta debugging: drop chunks of operations while the run still fails.
fn shrink(mut ops: Vec<Op>) -> Vec<Op> {
    let mut chunk = ops.len() / 2;
    while chunk > 0 {
        let mut i = 0;
        while i < ops.len() {
            let mut t = ops.clone();
            t.drain(i..(i + chunk).min(ops.len()));
            if fails(&t).is_some() {
                ops = t;
            } else {
                i += chunk;
            }
        }
        chunk /= 2;
    }
    ops
}

fn main() {
    let args: Vec<u64> = std::env::args()
        .skip(1)
        .filter_map(|a| a.parse().ok())
        .collect();
    let (first, last) = (
        args.first().copied().unwrap_or(1),
        args.get(1).copied().unwrap_or(100),
    );
    let len = args.get(2).copied().unwrap_or(2000) as usize;
    std::panic::set_hook(Box::new(|_| {}));
    let mut failures = 0;
    for seed in first..=last {
        let ops = sequence(seed, len);
        let Some(why) = fails(&ops) else { continue };
        failures += 1;
        let min = shrink(ops);
        println!("seed {seed}: {why}");
        println!("  minimal ({} ops): {:?}", min.len(), min);
        println!("  now fails with: {}", fails(&min).unwrap_or_default());
    }
    println!("seeds {first}..={last}: {failures} failing");
    std::process::exit((failures > 0) as i32);
}
