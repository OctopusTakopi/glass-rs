/-
Bit-scan helpers of `src/lib.rs`, proved correct.

What is modelled
* `u64` / `usize` values are `BitVec 64` (x86-64: `usize` is 64 bits). `u32`
  keys are `BitVec 32`. Rust's `u32` results of `trailing_zeros` etc. are
  widened with `as usize`, which preserves the value, so they are `BitVec 64`
  here too.
* Rust's documented integer methods (`trailing_zeros`, `leading_zeros`,
  `count_ones`) are core `BitVec.ctz` / `clz` / `cpop`; `*_spec` theorems
  below check these mean what the Rust docs say.
* The x86 intrinsics (`_tzcnt_u64`, `_lzcnt_u64`, `_blsr_u64`, `_bzhi_u64`,
  `_pdep_u64`, `_popcnt64`) are transcribed separately from the Intel SDM
  pseudocode, never defined via the Rust functions.
* Each helper is transcribed with both arms; the runtime CPU-feature flag
  (`has_bmi1`, `has_bmi2`, `has_lzcnt`, `has_popcnt`) is a `Bool` parameter.

What is assumed
* The SDM pseudocode is the intrinsic's semantics, and `core::arch` maps
  each intrinsic to that instruction.
* Callers respect the contracts noted per helper (checked in `src/lib.rs`).
-/
import GlassProof.Basic
import Std.Tactic.BVDecide

namespace Glass.Bits

/-- Bit `i` of `x` for a runtime index `i`, i.e. `(x >> i) & 1 == 1`. -/
def bitAt (x i : BitVec 64) : Prop := (x >>> i) &&& 1#64 = 1#64

/-- `bitAt` is the ordinary bit test. -/
theorem bitAt_iff (x i : BitVec 64) : bitAt x i ↔ x.getLsbD i.toNat = true := by
  have h0 : ∀ y : BitVec 64, (y &&& 1#64 = 1#64 ↔ y.getLsbD 0 = true) := by
    intro y; bv_decide
  simp only [bitAt, h0, BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight, Nat.add_zero]

/-! ## Rust integer methods (documented semantics) -/

/-- `u64::trailing_zeros`: number of trailing zero bits; 64 for 0. -/
def trailingZeros (x : BitVec 64) : BitVec 64 := x.ctz

/-- `u64::leading_zeros`: number of leading zero bits; 64 for 0. -/
def leadingZeros (x : BitVec 64) : BitVec 64 := x.clz

/-- `u64::count_ones`: number of one bits. -/
def countOnes (x : BitVec 64) : BitVec 64 := x.cpop

theorem trailingZeros_spec (x : BitVec 64) :
    (x = 0#64 → trailingZeros x = 64#64) ∧
    (x ≠ 0#64 → trailingZeros x < 64#64 ∧ bitAt x (trailingZeros x) ∧
      ∀ j, j < trailingZeros x → ¬ bitAt x j) := by
  simp only [trailingZeros, bitAt, BitVec.ctz]
  refine ⟨by bv_decide, fun h => ⟨by bv_decide, by bv_decide, fun j => by bv_decide⟩⟩

theorem leadingZeros_spec (x : BitVec 64) :
    (x = 0#64 → leadingZeros x = 64#64) ∧
    (x ≠ 0#64 → leadingZeros x < 64#64 ∧ bitAt x (63#64 - leadingZeros x) ∧
      ∀ j, 63#64 - leadingZeros x < j → j < 64#64 → ¬ bitAt x j) := by
  simp only [leadingZeros, bitAt]
  refine ⟨by bv_decide, fun h => ⟨by bv_decide, by bv_decide, fun j => by bv_decide⟩⟩

/-! ## x86 intrinsics (Intel SDM pseudocode) -/

/-- TZCNT: `temp ← 0; while temp < 64 and SRC[temp] = 0: temp++; DEST ← temp`. -/
def tzcntLoop (x : BitVec 64) : Nat → Nat → BitVec 64
  | 0, t => BitVec.ofNat 64 t
  | f + 1, t => if x.getLsbD t then BitVec.ofNat 64 t else tzcntLoop x f (t + 1)

def tzcnt (x : BitVec 64) : BitVec 64 := tzcntLoop x 64 0

/-- LZCNT: `temp ← 63; dest ← 0; while temp ≥ 0 and SRC[temp] = 0: temp--, dest++`.
Here `n` counts the zeros seen so far, so `temp = 63 - n`. -/
def lzcntLoop (x : BitVec 64) : Nat → Nat → BitVec 64
  | 0, n => BitVec.ofNat 64 n
  | f + 1, n => if x.getLsbD (63 - n) then BitVec.ofNat 64 n else lzcntLoop x f (n + 1)

def lzcnt (x : BitVec 64) : BitVec 64 := lzcntLoop x 64 0

/-- BLSR: `temp ← (SRC - 1) bitwiseAND (SRC)`. -/
def blsr (x : BitVec 64) : BitVec 64 := (x - 1#64) &&& x

/-- BZHI: `N ← INDEX[7:0]; DEST ← SRC; IF N < 64: DEST[63:N] ← 0`.
Clearing bits `63..N` is written as shifting them out and back. -/
def bzhi (src : BitVec 64) (index : BitVec 32) : BitVec 64 :=
  let n : BitVec 64 := (index &&& 0xFF#32).setWidth 64
  if n < 64#64 then (src <<< (64#64 - n)) >>> (64#64 - n) else src

/-- PDEP's counter `k` on entry to iteration `m` of
`for m in 0..64: if MASK[m] { DEST[m] ← TEMP[k]; k ← k + 1 }`. -/
def pdepK (mask : BitVec 64) : Nat → BitVec 64
  | 0 => 0#64
  | m + 1 => pdepK mask m + (if mask.getLsbD m then 1#64 else 0#64)

/-- PDEP's `DEST` after iterations `0..m` (DEST starts at 0). -/
def pdepD (src mask : BitVec 64) : Nat → BitVec 64
  | 0 => 0#64
  | m + 1 => pdepD src mask m |||
      (if mask.getLsbD m then ((src >>> pdepK mask m) &&& 1#64) <<< m else 0#64)

def pdep (src mask : BitVec 64) : BitVec 64 := pdepD src mask 64

/-- POPCNT: `count ← 0; for i in 0..64: if SRC[i] = 1 { count++ }`. -/
def popcntLoop (x : BitVec 64) : Nat → BitVec 64
  | 0 => 0#64
  | i + 1 => popcntLoop x i + (if x.getLsbD i then 1#64 else 0#64)

def popcnt (x : BitVec 64) : BitVec 64 := popcntLoop x 64

/-! ## The helpers, both arms -/

/-- `tz64`, src/lib.rs:1931. -/
def tz64 (has_bmi1 : Bool) (mask : BitVec 64) : BitVec 64 :=
  if has_bmi1 then tzcnt mask else trailingZeros mask

/-- `clear_lowest_bit`, src/lib.rs:1941 (`mask & mask.wrapping_sub(1)`). -/
def clearLowestBit (has_bmi1 : Bool) (mask : BitVec 64) : BitVec 64 :=
  if has_bmi1 then blsr mask else mask &&& (mask - 1#64)

/-- `popcnt64`, src/lib.rs:1953 (`_popcnt64(mask as i64)`: same bits). -/
def popcnt64 (has_popcnt : Bool) (mask : BitVec 64) : BitVec 64 :=
  if has_popcnt then popcnt mask else countOnes mask

/-- `high_bit`, src/lib.rs:1964. Contract: `mask ≠ 0` (otherwise `63 - 64`
underflows, a panic in debug builds, on both arms). -/
def highBit (has_lzcnt : Bool) (mask : BitVec 64) : BitVec 64 :=
  if has_lzcnt then 63#64 - lzcnt mask else 63#64 - leadingZeros mask

/-- `find_next_set_bit`, src/lib.rs:1973. -/
def findNextSetBit (has_bmi1 : Bool) (mask start : BitVec 64) : Option (BitVec 64) :=
  if 64#64 ≤ start then none
  else
    let m := mask >>> start
    if m = 0#64 then none else some (start + tz64 has_bmi1 m)

/-- `find_prev_set_bit`, src/lib.rs:1985 (x86-64 build: BZHI arm when
`has_bmi2`, else the shift-mask arm, which is also the non-x86 build). -/
def findPrevSetBit (has_bmi2 has_lzcnt : Bool) (mask end_ : BitVec 64) :
    Option (BitVec 64) :=
  if end_ = 0#64 then none
  else
    let m :=
      if has_bmi2 then bzhi mask (end_.setWidth 32)
      else if end_ < 64#64 then mask &&& ((1#64 <<< end_) - 1#64) else mask
    if m = 0#64 then none else some (highBit has_lzcnt m)

/-- The portable loop `for _ in 0..k { m &= m.wrapping_sub(1) }`. -/
def blsrIter : Nat → BitVec 64 → BitVec 64
  | 0, m => m
  | n + 1, m => blsrIter n (m &&& (m - 1#64))

/-- `select_kth_set_bit`, src/lib.rs:1849. Contract: `k < popcount(mask)`,
so `k < 64` and `1u64 << k` is in range. -/
def selectKthSetBit (has_bmi2 : Bool) (mask : BitVec 64) (k : Nat) : BitVec 64 :=
  if has_bmi2 then tzcnt (pdep (1#64 <<< k) mask)
  else trailingZeros (blsrIter k mask)

/-! ## Intrinsic arm = portable arm -/

set_option maxRecDepth 8000

theorem tzcnt_eq_trailingZeros (x : BitVec 64) : tzcnt x = trailingZeros x := by
  simp only [tzcnt, tzcntLoop, trailingZeros, BitVec.ctz]
  bv_decide

theorem lzcnt_eq_leadingZeros (x : BitVec 64) : lzcnt x = leadingZeros x := by
  simp only [lzcnt, lzcntLoop, leadingZeros]
  bv_decide

theorem popcnt_eq_countOnes (x : BitVec 64) : popcnt x = countOnes x := by
  simp only [popcnt, popcntLoop, countOnes]
  bv_decide

/-- `tz64`: both arms agree on every input (TZCNT and `trailing_zeros` both
return 64 for 0). -/
theorem tz64_arms (x : BitVec 64) : tz64 true x = tz64 false x := by
  simp only [tz64, if_true, tzcnt_eq_trailingZeros]; rfl

theorem clearLowestBit_arms (x : BitVec 64) : clearLowestBit true x = clearLowestBit false x := by
  simp only [clearLowestBit, blsr, if_true]
  bv_decide

theorem popcnt64_arms (x : BitVec 64) : popcnt64 true x = popcnt64 false x := by
  simp only [popcnt64, if_true, popcnt_eq_countOnes]; rfl

/-- `high_bit`: both arms agree on every input (for 0 both compute the same
wrapped `63 - 64`; callers never pass 0). -/
theorem highBit_arms (x : BitVec 64) : highBit true x = highBit false x := by
  simp only [highBit, if_true, lzcnt_eq_leadingZeros]; rfl

theorem findNextSetBit_arms (mask start : BitVec 64) :
    findNextSetBit true mask start = findNextSetBit false mask start := by
  simp only [findNextSetBit, tz64_arms]

/-- BZHI and the shift-mask fallback agree for every `end ≤ 255`; callers pass
`end ≤ NUM_CHILDREN = 64`. (At `end = 256` they differ: BZHI reads only the
low 8 bits of the index.) -/
theorem bzhi_eq_fallback (mask end_ : BitVec 64) (h : end_ < 256#64) :
    bzhi mask (end_.setWidth 32) =
      (if end_ < 64#64 then mask &&& ((1#64 <<< end_) - 1#64) else mask) := by
  simp only [bzhi]
  bv_decide

theorem findPrevSetBit_arms (mask end_ : BitVec 64) (l : Bool) (h : end_ < 256#64) :
    findPrevSetBit true l mask end_ = findPrevSetBit false l mask end_ := by
  simp only [findPrevSetBit, if_true, bzhi_eq_fallback mask end_ h]
  rfl

/-! ## Portable arm meets the mathematical spec -/

/-- `high_bit` returns the index of the highest set bit. -/
theorem highBit_spec (l : Bool) (x : BitVec 64) (hx : x ≠ 0#64) :
    highBit l x < 64#64 ∧ bitAt x (highBit l x) ∧
      ∀ j, highBit l x < j → j < 64#64 → ¬ bitAt x j := by
  have : highBit l x = highBit false x := by cases l <;> simp [highBit_arms]
  rw [this]
  simp only [highBit, Bool.false_eq_true, if_false, leadingZeros, bitAt]
  exact ⟨by bv_decide, by bv_decide, fun j => by bv_decide⟩

/-- `find_next_set_bit mask start` is the least set bit at or after `start`. -/
theorem findNextSetBit_spec (b : Bool) (mask start : BitVec 64) :
    (∀ i, findNextSetBit b mask start = some i →
      start < 64#64 ∧ start ≤ i ∧ i < 64#64 ∧ bitAt mask i ∧
      ∀ j, start ≤ j → j < i → ¬ bitAt mask j) ∧
    (findNextSetBit b mask start = none →
      ∀ j, start ≤ j → j < 64#64 → ¬ bitAt mask j) := by
  have : findNextSetBit b mask start = findNextSetBit false mask start := by
    cases b <;> simp [findNextSetBit_arms]
  rw [this]
  simp only [findNextSetBit, tz64, Bool.false_eq_true, if_false, trailingZeros, BitVec.ctz, bitAt]
  constructor
  · intro i hi
    split at hi
    · cases hi
    · split at hi
      · cases hi
      · cases hi
        exact ⟨by bv_decide, by bv_decide, by bv_decide, by bv_decide, fun j => by bv_decide⟩
  · intro hn j
    split at hn
    · bv_decide
    · split at hn
      · bv_decide
      · cases hn

/-- `find_prev_set_bit mask end` (for the `end ≤ 64` callers use) is the
greatest set bit strictly below `end`. -/
theorem findPrevSetBit_spec (b l : Bool) (mask end_ : BitVec 64) (hend : end_ ≤ 64#64) :
    (∀ i, findPrevSetBit b l mask end_ = some i →
      i < end_ ∧ bitAt mask i ∧ ∀ j, i < j → j < end_ → ¬ bitAt mask j) ∧
    (findPrevSetBit b l mask end_ = none → ∀ j, j < end_ → ¬ bitAt mask j) := by
  have : findPrevSetBit b l mask end_ = findPrevSetBit false false mask end_ := by
    have h256 : end_ < 256#64 := by bv_decide
    cases b
    · cases l <;> simp [findPrevSetBit, highBit_arms]
    · rw [findPrevSetBit_arms mask end_ l h256]
      cases l <;> simp [findPrevSetBit, highBit_arms]
  rw [this]
  have hform : findPrevSetBit false false mask end_ =
      if end_ = 0#64 then none else
        if (if end_ < 64#64 then mask &&& ((1#64 <<< end_) - 1#64) else mask) = 0#64 then none
        else some (63#64 -
          (if end_ < 64#64 then mask &&& ((1#64 <<< end_) - 1#64) else mask).clz) := rfl
  rw [hform]
  generalize hM : (if end_ < 64#64 then mask &&& ((1#64 <<< end_) - 1#64) else mask) = M
  simp only [bitAt]
  constructor
  · intro i hi
    by_cases h0 : end_ = 0#64
    · rw [if_pos h0] at hi; cases hi
    · rw [if_neg h0] at hi
      by_cases hm : M = 0#64
      · rw [if_pos hm] at hi; cases hi
      · rw [if_neg hm] at hi
        cases hi
        exact ⟨by bv_decide, by bv_decide, fun j => by bv_decide⟩
  · intro hn j
    by_cases h0 : end_ = 0#64
    · bv_decide
    · rw [if_neg h0] at hn
      by_cases hm : M = 0#64
      · bv_decide
      · rw [if_neg hm] at hn; cases hn

/-! ## `select_kth_set_bit` -/

/-- Bits of `mask` at positions `≥ t` (for `t ≤ 64`; `t = 64` gives 0). -/
def hiPart (mask t : BitVec 64) : BitVec 64 := mask &&& ~~~((1#64 <<< t) - 1#64)

/-- Bits of `mask` at positions `< t`. -/
def loPart (mask t : BitVec 64) : BitVec 64 := mask &&& ((1#64 <<< t) - 1#64)

theorem cpop_le_64 (mask : BitVec 64) : mask.cpop ≤ 64#64 := by bv_decide

/- Popcount identities are hard for SAT, so they go through core's
`cpop x = ofNat (cpopNatRec x 64 0)` by induction instead. -/

theorem cpopNatRec_or_disjoint (a b : BitVec 64) (h : a &&& b = 0#64) :
    ∀ n acc acc', (a ||| b).cpopNatRec n (acc + acc') =
      a.cpopNatRec n acc + b.cpopNatRec n acc' := by
  intro n
  induction n with
  | zero => intro acc acc'; rfl
  | succ n ih =>
    intro acc acc'
    simp only [BitVec.cpopNatRec_succ]
    have hbit : ((a ||| b).getLsbD n).toNat = (a.getLsbD n).toNat + (b.getLsbD n).toNat := by
      have := congrArg (fun x => x.getLsbD n) h
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero] at this
      simp only [BitVec.getLsbD_or]
      cases ha : a.getLsbD n <;> cases hb : b.getLsbD n <;> simp_all
    rw [hbit, ← ih]
    congr 1
    omega

/-- Popcount is additive over disjoint bits. -/
theorem cpop_or_disjoint (a b : BitVec 64) (h : a &&& b = 0#64) :
    (a ||| b).cpop = a.cpop + b.cpop := by
  simp only [BitVec.cpop]
  rw [← BitVec.ofNat_add, ← cpopNatRec_or_disjoint a b h 64 0 0]

theorem cpop_split (mask t : BitVec 64) :
    (loPart mask t).cpop + (hiPart mask t).cpop = mask.cpop := by
  have hd : loPart mask t &&& hiPart mask t = 0#64 := by
    simp only [loPart, hiPart]; bv_decide
  have hu : loPart mask t ||| hiPart mask t = mask := by
    simp only [loPart, hiPart]; bv_decide
  rw [← cpop_or_disjoint _ _ hd, hu]

theorem cpop_one_shl (c : BitVec 64) (hc : c < 64#64) : (1#64 <<< c).cpop = 1#64 := by
  bv_decide

theorem hiPart_zero (mask : BitVec 64) : hiPart mask 0#64 = mask := by
  simp only [hiPart]; bv_decide

theorem loPart_zero (mask : BitVec 64) : (loPart mask 0#64).cpop = 0#64 := by
  simp only [loPart]; bv_decide

/-- One loop iteration clears exactly the lowest remaining set bit: the
cleared prefix grows to just past it and gains one set bit. -/
theorem blsr_step (mask t : BitVec 64) (ht : t ≤ 64#64) (hne : hiPart mask t ≠ 0#64) :
    hiPart mask t &&& (hiPart mask t - 1#64) = hiPart mask ((hiPart mask t).ctz + 1#64) ∧
    (hiPart mask t).ctz + 1#64 ≤ 64#64 ∧
    (loPart mask ((hiPart mask t).ctz + 1#64)).cpop = (loPart mask t).cpop + 1#64 := by
  have hc : (hiPart mask t).ctz < 64#64 := by
    simp only [hiPart, BitVec.ctz] at *; bv_decide
  have hu : loPart mask ((hiPart mask t).ctz + 1#64) =
      loPart mask t ||| (1#64 <<< (hiPart mask t).ctz) := by
    simp only [hiPart, loPart, BitVec.ctz] at *; bv_decide
  have hd : loPart mask t &&& (1#64 <<< (hiPart mask t).ctz) = 0#64 := by
    simp only [hiPart, loPart, BitVec.ctz] at *; bv_decide
  refine ⟨?_, ?_, ?_⟩
  · simp only [hiPart, BitVec.ctz] at *; bv_decide
  · simp only [hiPart, BitVec.ctz] at *; bv_decide
  · rw [hu, cpop_or_disjoint _ _ hd, cpop_one_shl _ hc]

/-- The lowest bit left after clearing a prefix is a set bit of `mask`, with
exactly the prefix's set bits below it. -/
theorem select_final (mask t : BitVec 64) (ht : t ≤ 64#64) (hne : hiPart mask t ≠ 0#64) :
    (hiPart mask t).ctz < 64#64 ∧ bitAt mask (hiPart mask t).ctz ∧
    (loPart mask (hiPart mask t).ctz).cpop = (loPart mask t).cpop := by
  have hlo : loPart mask (hiPart mask t).ctz = loPart mask t := by
    simp only [hiPart, loPart, BitVec.ctz] at *; bv_decide
  refine ⟨?_, ?_, by rw [hlo]⟩
  · simp only [hiPart, BitVec.ctz] at *; bv_decide
  · simp only [hiPart, bitAt, BitVec.ctz] at *; bv_decide

theorem blsrIter_succ' (n : Nat) (m : BitVec 64) :
    blsrIter (n + 1) m = blsrIter n m &&& (blsrIter n m - 1#64) := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih => exact ih (m &&& (m - 1#64))

theorem ofNat_eq_cpop_toNat {n : Nat} {x : BitVec 64} (h : BitVec.ofNat 64 n = x)
    (hn : n ≤ x.toNat) : n = x.toNat := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  have hx := x.isLt
  omega

/-- After `n ≤ popcount(mask)` loop iterations, the loop variable is `mask`
with a prefix cleared that holds exactly `n` set bits. -/
theorem blsrIter_inv (mask : BitVec 64) :
    ∀ n : Nat, n ≤ mask.cpop.toNat →
      ∃ t : BitVec 64, t ≤ 64#64 ∧ blsrIter n mask = hiPart mask t ∧
        (loPart mask t).cpop = BitVec.ofNat 64 n := by
  intro n
  induction n with
  | zero => exact fun _ => ⟨0#64, by bv_decide, (hiPart_zero mask).symm, loPart_zero mask⟩
  | succ n ih =>
    intro hn
    obtain ⟨t, ht, hit, hcnt⟩ := ih (by omega)
    have hne : hiPart mask t ≠ 0#64 := by
      intro h0
      have hs := cpop_split mask t
      rw [h0, hcnt] at hs
      have : (0#64 : BitVec 64).cpop = 0#64 := by bv_decide
      rw [this, BitVec.add_zero] at hs
      have := ofNat_eq_cpop_toNat hs (by omega)
      omega
    obtain ⟨h1, h2, h3⟩ := blsr_step mask t ht hne
    refine ⟨(hiPart mask t).ctz + 1#64, h2, ?_, ?_⟩
    · rw [blsrIter_succ', hit, h1]
    · rw [h3, hcnt, BitVec.ofNat_add]

/-- The portable arm of `select_kth_set_bit` returns the `k`-th (0-based) set
bit of `mask`: a set bit with exactly `k` set bits below it. -/
theorem selectKthSetBit_loop_spec (mask : BitVec 64) (k : Nat) (hk : k < mask.cpop.toNat) :
    selectKthSetBit false mask k < 64#64 ∧ bitAt mask (selectKthSetBit false mask k) ∧
    (loPart mask (selectKthSetBit false mask k)).cpop = BitVec.ofNat 64 k := by
  obtain ⟨t, ht, hit, hcnt⟩ := blsrIter_inv mask k (by omega)
  have hne : hiPart mask t ≠ 0#64 := by
    intro h0
    have hs := cpop_split mask t
    rw [h0, hcnt] at hs
    have : (0#64 : BitVec 64).cpop = 0#64 := by bv_decide
    rw [this, BitVec.add_zero] at hs
    have := ofNat_eq_cpop_toNat hs (by omega)
    omega
  simp only [selectKthSetBit, Bool.false_eq_true, if_false, trailingZeros, hit]
  obtain ⟨h1, h2, h3⟩ := select_final mask t ht hne
  exact ⟨h1, h2, h3.trans hcnt⟩

/-- The loop with its trip count written as a guard on `k`, so the whole
equivalence below is one bit-vector formula with `k` symbolic. -/
def blsrGuarded (k : BitVec 64) : Nat → Nat → BitVec 64 → BitVec 64
  | 0, _, m => m
  | f + 1, i, m => blsrGuarded k f (i + 1) (if BitVec.ofNat 64 i < k then m &&& (m - 1#64) else m)

theorem blsrGuarded_eq (k : Nat) (hk : k ≤ 64) :
    ∀ f i (m : BitVec 64), i + f = 64 → blsrGuarded (BitVec.ofNat 64 k) f i m = blsrIter (k - i) m := by
  intro f
  induction f with
  | zero =>
    intro i m h
    have : k - i = 0 := by omega
    simp [blsrGuarded, this, blsrIter]
  | succ f ih =>
    intro i m h
    simp only [blsrGuarded]
    by_cases hik : i < k
    · have hlt : BitVec.ofNat 64 i < BitVec.ofNat 64 k := by
        simp only [BitVec.lt_def, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact hik
      rw [if_pos hlt, ih (i + 1) _ (by omega)]
      have : k - i = (k - (i + 1)) + 1 := by omega
      rw [this]; rfl
    · have hlt : ¬ BitVec.ofNat 64 i < BitVec.ofNat 64 k := by
        simp only [BitVec.lt_def, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact hik
      rw [if_neg hlt, ih (i + 1) _ (by omega)]
      have h1 : k - (i + 1) = 0 := by omega
      have h2 : k - i = 0 := by omega
      rw [h1, h2]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
/-- PDEP select equals the portable loop, for every mask and every `k < 64`.
One SAT query; takes ~11 minutes to check. -/
theorem select_pdep_eq_loop (mask k : BitVec 64) (hk : k < 64#64) :
    (pdep (1#64 <<< k) mask).ctz = (blsrGuarded k 64 0 mask).ctz := by
  simp only [pdep, pdepD, pdepK, blsrGuarded, BitVec.ctz]
  bv_decide (config := { timeout := 1800 })

/-- `select_kth_set_bit`: both arms agree for every `k < 64` (including
`k ≥ popcount(mask)`, where both return 64). -/
theorem selectKthSetBit_arms (mask : BitVec 64) (k : Nat) (hk : k < 64) :
    selectKthSetBit true mask k = selectKthSetBit false mask k := by
  simp only [selectKthSetBit, if_true, Bool.false_eq_true, if_false,
    tzcnt_eq_trailingZeros, trailingZeros]
  have hs : (1#64 <<< k) = 1#64 <<< (BitVec.ofNat 64 k) := by
    simp only [BitVec.shiftLeft_eq', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]
  have hkb : BitVec.ofNat 64 k < 64#64 := by
    simp only [BitVec.lt_def, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]; exact hk
  rw [hs, select_pdep_eq_loop mask _ hkb, blsrGuarded_eq k (by omega) 64 0 mask rfl, Nat.sub_zero]

/-- `select_kth_set_bit` (either arm) returns the `k`-th set bit, under the
caller contract `k < popcount(mask)` (glass_find_kth_key). -/
theorem selectKthSetBit_spec (b : Bool) (mask : BitVec 64) (k : Nat) (hk : k < mask.cpop.toNat) :
    selectKthSetBit b mask k < 64#64 ∧ bitAt mask (selectKthSetBit b mask k) ∧
    (loPart mask (selectKthSetBit b mask k)).cpop = BitVec.ofNat 64 k := by
  have h64 : k < 64 := by
    have := cpop_le_64 mask
    simp only [BitVec.le_def] at this
    have : (64#64).toNat = 64 := rfl
    omega
  cases b
  · exact selectKthSetBit_loop_spec mask k hk
  · rw [selectKthSetBit_arms mask k h64]; exact selectKthSetBit_loop_spec mask k hk

/-! ## Key layout -/

/-- A `u32` key splits into its leaf's partial key `key >> 6` and slot
`key & 63`, and `(partial << 6) | slot` rebuilds it (glass_min/glass_next). -/
theorem key_split (key : BitVec 32) : ((key >>> 6) <<< 6) ||| (key &&& 63#32) = key := by
  bv_decide

/-- The buy/sell paths form prices as `base | slot` with
`base = (ht_k as u64) << 6`; that OR is an addition, and the price is the
original `u32` key. Live leaves have `ht_k = key >> 6 < 2^26`; without that
bound the `u32` round-trip is false (e.g. `ht_k = u32::MAX`, the value
`ht_remove` leaves in a freed leaf). -/
theorem price_or_eq_add (htk : BitVec 32) (slot : BitVec 64) (hk : htk < 0x4000000#32)
    (h : slot < 64#64) :
    (htk.setWidth 64 <<< 6) ||| slot = (htk.setWidth 64 <<< 6) + slot ∧
    (htk.setWidth 64 <<< 6) ||| slot = ((htk <<< 6) ||| slot.setWidth 32).setWidth 64 := by
  constructor <;> bv_decide

/-- Nat form of the same fact. -/
theorem nat_or_eq_add (base slot : Nat) (hb : base % 64 = 0) (hs : slot < 64) :
    base ||| slot = base + slot := by
  have hbase : base = 2 ^ 6 * (base / 64) := by omega
  rw [hbase, ← Nat.two_pow_add_eq_or_of_lt (by omega)]

/-- Trie slot of a partial key at internal level `l ∈ 0..4`:
`(partial >> ((NUM_LEVELS - 2 - l) * 6)) & 0x3F` (trie_find_leaf,
detach_leaf_from_trie, decrement_ancestor_counts). -/
def digit (l : Nat) (p : BitVec 32) : BitVec 32 := (p >>> ((4 - l) * 6)) &&& 63#32

/-- Partial keys of `u32` keys fit the five 6-bit levels. -/
theorem partial_lt (key : BitVec 32) : key >>> 6 < 0x4000000#32 := by bv_decide

/-- Distinct partial keys take distinct trie paths. -/
theorem digits_injective (p q : BitVec 32) (hp : p < 0x4000000#32) (hq : q < 0x4000000#32)
    (h0 : digit 0 p = digit 0 q) (h1 : digit 1 p = digit 1 q) (h2 : digit 2 p = digit 2 q)
    (h3 : digit 3 p = digit 3 q) (h4 : digit 4 p = digit 4 q) : p = q := by
  simp only [digit] at *
  bv_decide

/-- Lexicographic order on trie paths is numeric order on partial keys, so
an in-order walk of the trie (and the leaf list it maintains) is sorted. -/
theorem digits_lex_iff_lt (p q : BitVec 32) (hp : p < 0x4000000#32) (hq : q < 0x4000000#32) :
    p < q ↔
      (digit 0 p < digit 0 q ∨ digit 0 p = digit 0 q ∧
      (digit 1 p < digit 1 q ∨ digit 1 p = digit 1 q ∧
      (digit 2 p < digit 2 q ∨ digit 2 p = digit 2 q ∧
      (digit 3 p < digit 3 q ∨ digit 3 p = digit 3 q ∧
       digit 4 p < digit 4 q)))) := by
  simp only [digit]
  bv_decide

/-- Keys order by (partial key, slot) lexicographically: the leaf list sorted
by partial key, each leaf scanned by slot, visits keys in increasing order. -/
theorem key_lex_iff_lt (a b : BitVec 32) :
    a < b ↔ (a >>> 6 < b >>> 6 ∨ a >>> 6 = b >>> 6 ∧ a &&& 63#32 < b &&& 63#32) := by
  bv_decide

/-- `glass_find_kth_key` rebuilds a key as
`Σ_depth (slot_depth << ((5 - depth) * 6)) | leaf_slot`; with the slots taken
from the key's own trie path this is the key. -/
theorem key_rebuild (key : BitVec 32) :
    (digit 0 (key >>> 6) <<< 30) ||| (digit 1 (key >>> 6) <<< 24) |||
      (digit 2 (key >>> 6) <<< 18) ||| (digit 3 (key >>> 6) <<< 12) |||
      (digit 4 (key >>> 6) <<< 6) ||| (key &&& 63#32) = key := by
  simp only [digit]
  bv_decide

end Glass.Bits
