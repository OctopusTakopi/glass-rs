//! libFuzzer entry point; the harness is `glass_rs_fuzz::run` (src/lib.rs).

#![no_main]

use libfuzzer_sys::fuzz_target;

// Capped so a single input stays fast; `walk` runs long sequences.
fuzz_target!(|ops: Vec<glass_rs_fuzz::Op>| glass_rs_fuzz::run(&ops[..ops.len().min(400)]));
