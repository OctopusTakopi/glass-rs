use criterion::{Criterion, criterion_group, criterion_main};
use glass_rs::Glass;
use rand::distr::Uniform;
use rand::prelude::*;
use rand::rng;
use std::collections::BTreeMap;
use std::hint::black_box;
use std::time::Duration;

const N: usize = 1000000; // Number of operations for benchmarks

fn generate_random_keys(n: usize) -> Vec<u32> {
    let between = Uniform::try_from(500..2000).unwrap();
    let mut rng = rand::rng();
    (0..n).map(|_| between.sample(&mut rng)).collect()
}

fn generate_random_values(n: usize) -> Vec<u64> {
    let between = Uniform::try_from(1..1000).unwrap();
    let mut rng = rand::rng();
    (0..n).map(|_| between.sample(&mut rng)).collect()
}

fn bench_insert(c: &mut Criterion) {
    let keys = generate_random_keys(N);
    let values = generate_random_values(N);

    c.bench_function("insert", |b| {
        b.iter(|| {
            let mut glass = Glass::new();
            for i in 0..N {
                glass.insert(black_box(keys[i]), black_box(values[i]));
            }
        })
    });

    c.bench_function("insert_btree", |b| {
        b.iter(|| {
            let mut map = BTreeMap::new();
            for i in 0..N {
                map.insert(black_box(keys[i]), black_box(values[i]));
            }
        })
    });
}

fn bench_get(c: &mut Criterion) {
    let keys = generate_random_keys(N);
    let values = generate_random_values(N);
    let mut glass = Glass::new();
    for i in 0..N {
        glass.insert(keys[i], values[i]);
    }

    c.bench_function("get_existing", |b| {
        b.iter(|| {
            for &key in &keys {
                black_box(glass.get(key));
            }
        })
    });

    let non_keys: Vec<u32> = generate_random_keys(N)
        .into_iter()
        .map(|k| k.wrapping_add(1))
        .collect();

    c.bench_function("get_non_existing", |b| {
        b.iter(|| {
            for &key in &non_keys {
                black_box(glass.get(key));
            }
        })
    });

    let mut map = BTreeMap::new();
    for i in 0..N {
        map.insert(keys[i], values[i]);
    }

    c.bench_function("get_existing_btree", |b| {
        b.iter(|| {
            for &key in &keys {
                black_box(map.get(&key));
            }
        })
    });

    let non_keys: Vec<u32> = generate_random_keys(N)
        .into_iter()
        .map(|k| k.wrapping_add(1))
        .collect();

    c.bench_function("get_non_existing_btree", |b| {
        b.iter(|| {
            for &key in &non_keys {
                black_box(map.get(&key));
            }
        })
    });
}

fn bench_remove(c: &mut Criterion) {
    let keys = generate_random_keys(N);
    let values = generate_random_values(N);

    c.bench_function("remove", |b| {
        b.iter(|| {
            let mut glass = Glass::new();
            for i in 0..N {
                glass.insert(keys[i], values[i]);
            }
            for &key in &keys {
                black_box(glass.remove(key));
            }
        })
    });

    c.bench_function("remove_btree", |b| {
        b.iter(|| {
            let mut map = BTreeMap::new();
            for i in 0..N {
                map.insert(keys[i], values[i]);
            }
            for &key in &keys {
                black_box(map.remove(&key));
            }
        })
    });
}

fn bench_min_max(c: &mut Criterion) {
    let keys = generate_random_keys(N);
    let values = generate_random_values(N);
    let mut glass = Glass::new();
    for i in 0..N {
        glass.insert(keys[i], values[i]);
    }

    c.bench_function("min", |b| b.iter(|| black_box(glass.min())));
    c.bench_function("max", |b| b.iter(|| black_box(glass.max())));

    let mut map = BTreeMap::new();
    for i in 0..N {
        map.insert(keys[i], values[i]);
    }

    c.bench_function("min_btree", |b| b.iter(|| black_box(min_btree(&map))));
    c.bench_function("max_btree", |b| b.iter(|| black_box(max_btree(&map))));
}

fn bench_compute_buy_cost(c: &mut Criterion) {
    let keys = generate_random_keys(N);
    let values = generate_random_values(N);
    let mut glass = Glass::new();
    for i in 0..N {
        glass.insert(keys[i], values[i]);
    }
    let target = 1000u64;

    c.bench_function("compute_buy_cost", |b| {
        b.iter(|| black_box(glass.compute_buy_cost(black_box(target))))
    });

    let mut map = BTreeMap::new();
    for i in 0..N {
        map.insert(keys[i], values[i]);
    }
    let target = 1000u64;

    c.bench_function("compute_buy_cost_btree", |b| {
        b.iter(|| black_box(compute_buy_cost_btree(&map, black_box(target))))
    });
}

/// Benchmarks the `remove_by_index` function under different scenarios.
fn bench_remove_by_index(c: &mut Criterion) {
    let keys = generate_random_keys(N);
    let values = generate_random_values(N);

    let mut group = c.benchmark_group("remove_by_index");

    // Scenario 1: Always remove the smallest element (index 0).
    // This tests repeatedly finding and removing the minimum.
    group.bench_function("from_start", |b| {
        b.iter_with_setup(
            || {
                // Setup: Create a full glass.
                let mut glass = Glass::new();
                for i in 0..N {
                    glass.insert(keys[i], values[i]);
                }
                let size = glass.glass_size();
                (glass, size)
            },
            |(mut glass, size)| {
                // Routine: Drain the glass from the beginning.
                for _ in 0..size {
                    black_box(glass.remove_by_index(black_box(0)));
                }
            },
        )
    });

    // Scenario 2: Always remove the largest element.
    // This tests repeatedly finding and removing the maximum.
    group.bench_function("from_end", |b| {
        b.iter_with_setup(
            || {
                // Setup
                let mut glass = Glass::new();
                for i in 0..N {
                    glass.insert(keys[i], values[i]);
                }
                let size = glass.glass_size();
                (glass, size)
            },
            |(mut glass, size)| {
                // Routine: Drain the glass from the end.
                for i in 0..size {
                    let current_last_index = size - 1 - i;
                    black_box(glass.remove_by_index(black_box(current_last_index)));
                }
            },
        )
    });

    // Scenario 3: Remove a random element.
    // This tests the average case performance.
    group.bench_function("random", |b| {
        b.iter_with_setup(
            || {
                // Setup
                let mut glass = Glass::new();
                for i in 0..N {
                    glass.insert(keys[i], values[i]);
                }
                // FIX: Get the size *before* moving the glass.
                let size = glass.glass_size();
                (glass, size, rng())
            },
            |(mut glass, size, mut rng)| {
                // Routine: Drain the glass from random positions.
                for i in 0..size {
                    let current_size = size - i;
                    let k = rng.random_range(0..current_size);
                    black_box(glass.remove_by_index(black_box(k)));
                }
            },
        )
    });

    group.finish();
}

fn min_btree(map: &BTreeMap<u32, u64>) -> Option<(u32, u64)> {
    map.iter().next().map(|(&k, &v)| (k, v))
}

fn max_btree(map: &BTreeMap<u32, u64>) -> Option<(u32, u64)> {
    map.iter().next_back().map(|(&k, &v)| (k, v))
}

fn compute_buy_cost_btree(map: &BTreeMap<u32, u64>, target: u64) -> u64 {
    let mut remaining = target;
    let mut cost = 0u64;
    for (&price, &quantity) in map.iter() {
        if remaining == 0 {
            break;
        }
        let take = remaining.min(quantity);
        cost += price as u64 * take;
        remaining -= take;
    }
    cost
}

fn remove_by_index_btree(map: &mut BTreeMap<u32, u64>, index: usize) -> Option<(u32, u64)> {
    if index >= map.len() {
        return None;
    }
    let key = *map.keys().nth(index).unwrap();
    map.remove_entry(&key)
}

/// Benchmarks the remove_by_index function under different scenarios.
fn bench_remove_by_index_btree(c: &mut Criterion) {
    let keys = generate_random_keys(N);
    let values = generate_random_values(N);

    let mut group = c.benchmark_group("remove_by_index_btree");

    // Scenario 1: Always remove the smallest element (index 0).
    // This tests repeatedly finding and removing the minimum.
    group.bench_function("from_start", |b| {
        b.iter_with_setup(
            || {
                // Setup: Create a full map.
                let mut map = BTreeMap::new();
                for i in 0..N {
                    map.insert(keys[i], values[i]);
                }
                let size = map.len();
                (map, size)
            },
            |(mut map, size)| {
                // Routine: Drain the tree from the beginning.
                for _ in 0..size {
                    black_box(remove_by_index_btree(&mut map, black_box(0)));
                }
            },
        )
    });

    // Scenario 2: Always remove the largest element.
    // This tests repeatedly finding and removing the maximum.
    group.bench_function("from_end", |b| {
        b.iter_with_setup(
            || {
                // Setup
                let mut map = BTreeMap::new();
                for i in 0..N {
                    map.insert(keys[i], values[i]);
                }
                let size = map.len();
                (map, size)
            },
            |(mut map, size)| {
                // Routine: Drain the map from the end.
                for i in 0..size {
                    let current_last_index = size - 1 - i;
                    black_box(remove_by_index_btree(
                        &mut map,
                        black_box(current_last_index),
                    ));
                }
            },
        )
    });

    // Scenario 3: Remove a random element.
    // This tests the average case performance.
    group.bench_function("random", |b| {
        b.iter_with_setup(
            || {
                // Setup
                let mut map = BTreeMap::new();
                for i in 0..N {
                    map.insert(keys[i], values[i]);
                }
                // Get the size before moving the map.
                let size = map.len();
                (map, size, ThreadRng::default())
            },
            |(mut map, size, mut rng)| {
                // Routine: Drain the map from random positions.
                for i in 0..size {
                    let current_size = size - i;
                    let k = rng.random_range(0..current_size);
                    black_box(remove_by_index_btree(&mut map, black_box(k)));
                }
            },
        )
    });

    group.finish();
}

criterion_group! {
    name = benches;
    config = Criterion::default().measurement_time(Duration::from_secs(6));
    targets = bench_insert, bench_get, bench_remove, bench_min_max, bench_compute_buy_cost,
        bench_remove_by_index, bench_remove_by_index_btree
}

criterion_main!(benches);
