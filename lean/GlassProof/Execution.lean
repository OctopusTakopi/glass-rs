import GlassProof.Basic

/-!
# Order execution over the linked leaf list

Model of the leaf-sweep paths of `src/lib.rs`:

* `compute_buy_cost`  (src/lib.rs:1335-1395) → `computeBuyCost`
* `buy_shares`, glass part (src/lib.rs:1128-1210) → `sweep leafSums false` (`buyKernel`)
* `compute_sell_cost` (src/lib.rs:1510-1572) → `computeSellCost`
* `sell_shares`, glass part (src/lib.rs:1445-1500) → `sweep leafSums true` (`sellKernel`)
* `Glass::leaf_sums` (src/lib.rs:1074-1088) with `leaf_sums_scalar`
  (src/lib.rs:2090-2100) and `leaf_sums_wide` (src/lib.rs:2107-2116) → `leafSums`

against a greedy specification (`buySpec`: fill from the front of a level list,
partially filling the last level touched).

## What is modeled

* A leaf is its partial key `pkey` (`ht_k`) and its 64 dense quantities
  `vals` (`values`, 0 = empty). Price of slot `i` is `pkey * 64 + i`; the Rust
  computes it as `base | slot` with `base = ht_k << 6`, which equals
  `base + slot` for `slot < 64` (proved in `GlassProof.Bits`).
* **Representation assumption:** the occupancy `mask` is derived from `vals`
  (bit `i` set ↔ `vals[i] ≠ 0`). Every per-slot loop that walks set bits of
  the mask (`tz64` / `trailing_zeros` upward, `high_bit` / `leading_zeros`
  downward) is modeled as walking the dense cells and skipping zero cells.
* The linked leaf list (`min_leaf → next_leaf`, `max_leaf → prev_leaf`) is a
  Lean list of leaves; buy walks it front to back, sell walks its reverse.
* `u64` arithmetic uses the exact Rust semantics from `GlassProof.Basic`
  (`satAdd`/`satMul` clamp, `wrapAdd`/`wrapMul` reduce mod 2^64).
* `leaf_sums` is the scalar fast pass (wrapping sums plus an OR of all
  quantities), trusted when the OR is below `2^52`, else the `u128` re-sum.
  The AVX-512 fast pass (`leaf_sums_avx512`) computes the same three values
  (mod-2^64 sums in another association order, and the OR) and is **not**
  modeled.
* The loops are parameterised by the `leaf_sums` implementation `S`; the
  crate is `S := leafSums`, and `Legacy.legacySums` is the pre-fix one.

## What is abstracted away

* Tier routing, `restructure`, and the pinned `u32::MAX` level in
  `buy_shares` (covered by `GlassProof.Tiers`): the kernels here return when
  the glass tier is exhausted, with the unfilled share count.
* Cache bookkeeping that does not affect the returned cost or the remaining
  levels: `min_key`/`max_key`, ancestor `count`s, the intrusive hash table,
  the cached path, prefetches, arena free lists.

## Result

`leafSums_spec`: `leaf_sums` returns the exact quantity sum and the saturated
slot-weighted sum, or `none` exactly when the quantity sum exceeds `u64`.
Hence, for any leaves of ≤ 64 slots and any `u64` order size, every model
returns `min(exact greedy cost, u64::MAX)` and the kernels leave exactly the
spec's remaining levels (`buyKernel_correct`, `sellKernel_correct`,
`computeBuyCost_correct`, `computeSellCost_correct`); the partial walk's new
`m == 0` guard is never reached (`sweep_partial_fills`). The regression
theorems (`fixed_*`) run the three books that broke the pre-fix code; the
`Legacy` section keeps the pre-fix `leaf_sums` and proves it wrong on them
(`Legacy.cex_*`, the numbers the Rust crate printed before the fix).
-/

namespace Glass.Execution
open Glass

/-- A price level `(price, quantity)`. -/
abbrev Level := Nat × Nat

/-! ## Specification -/

/-- Greedy execution from the front of a level list: `(exact cost, shares left
unfilled, remaining levels)`. On a list sorted by ascending price this is a
market buy; on a descending list it is a market sell. -/
def buySpec : List Level → Nat → Nat × Nat × List Level
  | [], n => (0, n, [])
  | (p, q) :: rest, n =>
    if n = 0 then (0, 0, (p, q) :: rest)
    else if q ≤ n then
      let r := buySpec rest (n - q)
      (p * q + r.1, r.2.1, r.2.2)
    else (p * n, 0, (p, q - n) :: rest)

/-- Market sell against an ascending level list: greedy from the highest
price. Remaining levels are returned in ascending order. -/
def sellSpec (l : List Level) (n : Nat) : Nat × Nat × List Level :=
  let r := buySpec l.reverse n
  (r.1, r.2.1, r.2.2.reverse)

/-- Exact cost of taking every level of a list. -/
def cost : List Level → Nat
  | [] => 0
  | (p, q) :: l => p * q + cost l

/-- Total quantity of a list. -/
def qty : List Level → Nat
  | [] => 0
  | (_, q) :: l => q + qty l

/-- Strictly increasing prices (a well-formed ascending book side). -/
def Ascending : List Level → Prop
  | [] => True
  | (p, _) :: l => (∀ lv ∈ l, p < lv.1) ∧ Ascending l

theorem buySpec_zero (l : List Level) : buySpec l 0 = (0, 0, l) := by
  cases l with
  | nil => rfl
  | cons hd tl => obtain ⟨p, q⟩ := hd; simp [buySpec]

/-- Greedy execution over a concatenation runs the first part, then the
second part with whatever is left. -/
theorem buySpec_append (A B : List Level) (n : Nat) :
    buySpec (A ++ B) n =
      ((buySpec A n).1 + (buySpec B (buySpec A n).2.1).1,
       (buySpec B (buySpec A n).2.1).2.1,
       (buySpec A n).2.2 ++ (buySpec B (buySpec A n).2.1).2.2) := by
  induction A generalizing n with
  | nil => simp [buySpec]
  | cons hd A ih =>
    obtain ⟨p, q⟩ := hd
    by_cases hn : n = 0
    · subst hn; simp [buySpec, buySpec_zero]
    · by_cases hq : q ≤ n
      · simp [buySpec, hn, hq, ih, Nat.add_assoc]
      · simp [buySpec, hn, hq, buySpec_zero]

/-- If a list's total quantity is at most `n`, greedy execution takes all of
it. -/
theorem buySpec_all (A : List Level) (n : Nat) (hpos : ∀ lv ∈ A, 0 < lv.2)
    (h : qty A ≤ n) : buySpec A n = (cost A, n - qty A, []) := by
  induction A generalizing n with
  | nil => simp [buySpec, cost, qty]
  | cons hd A ih =>
    obtain ⟨p, q⟩ := hd
    have hq : 0 < q := hpos (p, q) (by simp)
    simp only [qty] at h
    have hn : n ≠ 0 := by omega
    have hqn : q ≤ n := by omega
    have := ih (n - q) (fun lv hlv => hpos lv (by simp [hlv])) (by omega)
    simp only [buySpec, hn, hqn, if_false, if_true, this, cost, qty]
    simp only [Prod.mk.injEq, and_true, true_and]
    omega

/-- If a list holds more than `n`, greedy execution fills all `n`. -/
theorem buySpec_short (A : List Level) (n : Nat) (h : n < qty A) :
    (buySpec A n).2.1 = 0 := by
  induction A generalizing n with
  | nil => simp [qty] at h
  | cons hd A ih =>
    obtain ⟨p, q⟩ := hd
    simp only [qty] at h
    by_cases hn : n = 0
    · subst hn; simp [buySpec]
    · by_cases hq : q ≤ n
      · simp only [buySpec, hn, hq, if_false, if_true]; exact ih (n - q) (by omega)
      · simp [buySpec, hn, hq]

/-- Greedy execution never leaves more unfilled than was asked. -/
theorem buySpec_unfilled_le (A : List Level) (n : Nat) : (buySpec A n).2.1 ≤ n := by
  induction A generalizing n with
  | nil => simp [buySpec]
  | cons hd A ih =>
    obtain ⟨p, q⟩ := hd
    by_cases hn : n = 0
    · subst hn; simp [buySpec]
    · by_cases hq : q ≤ n
      · simp only [buySpec, hn, hq, if_false, if_true]; have := ih (n - q); omega
      · simp [buySpec, hn, hq]

theorem qty_append (a b : List Level) : qty (a ++ b) = qty a + qty b := by
  induction a with
  | nil => simp [qty]
  | cons hd a ih => obtain ⟨p, q⟩ := hd; simp [qty, ih, Nat.add_assoc]

theorem cost_append (a b : List Level) : cost (a ++ b) = cost a + cost b := by
  induction a with
  | nil => simp [cost]
  | cons hd a ih => obtain ⟨p, q⟩ := hd; simp [cost, ih, Nat.add_assoc]

theorem qty_reverse (a : List Level) : qty a.reverse = qty a := by
  induction a with
  | nil => rfl
  | cons hd a ih => obtain ⟨p, q⟩ := hd; simp [qty, qty_append, ih]; omega

theorem cost_reverse (a : List Level) : cost a.reverse = cost a := by
  induction a with
  | nil => rfl
  | cons hd a ih => obtain ⟨p, q⟩ := hd; simp [cost, cost_append, ih]; omega

/-! ## Cells: the dense slots of a leaf -/

/-- Keep the occupied cells (quantity ≠ 0): the levels a leaf holds. -/
def nz : List Level → List Level
  | [] => []
  | (p, v) :: cs => if v = 0 then nz cs else (p, v) :: nz cs

theorem nz_append (a b : List Level) : nz (a ++ b) = nz a ++ nz b := by
  induction a with
  | nil => rfl
  | cons hd a ih => obtain ⟨p, v⟩ := hd; by_cases hv : v = 0 <;> simp [nz, hv, ih]

theorem nz_reverse (c : List Level) : nz c.reverse = (nz c).reverse := by
  induction c with
  | nil => rfl
  | cons hd c ih =>
    obtain ⟨p, v⟩ := hd
    by_cases hv : v = 0 <;> simp [nz, hv, nz_append, ih]

theorem nz_pos (c : List Level) : ∀ lv ∈ nz c, 0 < lv.2 := by
  induction c with
  | nil => simp [nz]
  | cons hd c ih =>
    obtain ⟨p, v⟩ := hd
    intro lv hlv
    by_cases hv : v = 0
    · simp only [nz, hv, if_true] at hlv; exact ih lv hlv
    · simp only [nz, hv, if_false, List.mem_cons] at hlv
      rcases hlv with rfl | hlv
      · simp only; omega
      · exact ih lv hlv

/-- Walk direction: `false` = ascending slots / leaves (buy side), `true` =
descending (sell side). -/
def orient {α : Type} (desc : Bool) (l : List α) : List α := if desc then l.reverse else l

theorem orient_orient {α : Type} (d : Bool) (l : List α) : orient d (orient d l) = l := by
  cases d <;> simp [orient]

theorem nz_orient (d : Bool) (c : List Level) : nz (orient d c) = orient d (nz c) := by
  cases d <;> simp [orient, nz_reverse]

theorem mem_orient {α : Type} {d : Bool} {l : List α} {a : α} : a ∈ orient d l ↔ a ∈ l := by
  cases d <;> simp [orient]

theorem map_orient {α β : Type} (d : Bool) (f : α → β) (l : List α) :
    (orient d l).map f = orient d (l.map f) := by
  cases d <;> simp [orient]

theorem qty_orient (d : Bool) (l : List Level) : qty (orient d l) = qty l := by
  cases d <;> simp [orient, qty_reverse]

theorem cost_orient (d : Bool) (l : List Level) : cost (orient d l) = cost l := by
  cases d <;> simp [orient, cost_reverse]

/-- Cells of a leaf from slot `i` on: `(price, quantity)` for every slot,
empty ones included. -/
def cellsFrom (base : Nat) : Nat → List Nat → List Level
  | _, [] => []
  | i, v :: vs => (base + i) |> fun p => (p, v) :: cellsFrom base (i + 1) vs

/-- Exact `Σ (i + j) * vs[j]`: the slot-weighted quantity sum. -/
def wsumFrom : Nat → List Nat → Nat
  | _, [] => 0
  | i, v :: vs => i * v + wsumFrom (i + 1) vs

theorem qty_cells (b i : Nat) (vs : List Nat) : qty (nz (cellsFrom b i vs)) = vs.sum := by
  induction vs generalizing i with
  | nil => rfl
  | cons v vs ih =>
    by_cases hv : v = 0
    · simp [cellsFrom, nz, hv, ih]
    · simp [cellsFrom, nz, hv, qty, ih]

/-- The whole-leaf cost identity behind the vectorized sweep:
`Σ (base + i) * v_i = base * Σ v_i + Σ i * v_i`. -/
theorem cost_cells (b i : Nat) (vs : List Nat) :
    cost (nz (cellsFrom b i vs)) = b * vs.sum + wsumFrom i vs := by
  induction vs generalizing i with
  | nil => simp [cellsFrom, nz, cost, wsumFrom]
  | cons v vs ih =>
    by_cases hv : v = 0
    · simp [cellsFrom, nz, hv, ih, wsumFrom]
    · simp only [cellsFrom, nz, hv, if_false, cost, ih, wsumFrom, List.sum_cons]
      simp only [Nat.add_mul, Nat.mul_add]; omega

/-- Rebuilding a leaf's dense values from cells whose prices are unchanged
gives back those cells. -/
theorem cells_rebuild (b : Nat) : ∀ (i : Nat) (vs : List Nat) (cs : List Level),
    cs.map Prod.fst = (cellsFrom b i vs).map Prod.fst →
    cellsFrom b i (cs.map Prod.snd) = cs
  | _, [], cs, h => by
    simp only [cellsFrom, List.map_nil, List.map_eq_nil_iff] at h; subst h; rfl
  | _, _ :: _, [], h => by simp [cellsFrom] at h
  | i, v :: vs, (p, w) :: cs, h => by
    simp only [cellsFrom, List.map_cons, List.cons.injEq] at h ⊢
    exact ⟨by rw [h.1], cells_rebuild b (i + 1) vs cs h.2⟩

/-! ## `leaf_sums`

The fixed `Glass::leaf_sums` (src/lib.rs:1074-1088) runs a fast wrapping
pass (`leaf_sums_scalar`, src/lib.rs:2090-2100; the AVX-512 path at
src/lib.rs:2154 computes the same three values and is not modeled), and trusts
it only when the OR of all quantities is below `LEAF_SUM_EXACT_BOUND = 2^52`;
otherwise it re-sums in `u128` out of line (`leaf_sums_wide`,
src/lib.rs:2107-2116). -/

/-- The wrapping sums of `leaf_sums_scalar` from slot `i`, with running
`(qty, weighted)`: `qty = qty.wrapping_add(v)`,
`weighted = weighted.wrapping_add((i as u64).wrapping_mul(v))`. -/
def leafSumsFrom : Nat → List Nat → Nat → Nat → Nat × Nat
  | _, [], q, w => (q, w)
  | i, v :: vs, q, w => leafSumsFrom (i + 1) vs (wrapAdd q v) (wrapAdd w (wrapMul i v))

theorem leafSumsFrom_eq (i : Nat) (vs : List Nat) (q w : Nat) (hq : q < 2 ^ 64)
    (hw : w < 2 ^ 64) :
    leafSumsFrom i vs q w = ((q + vs.sum) % 2 ^ 64, (w + wsumFrom i vs) % 2 ^ 64) := by
  induction vs generalizing i q w with
  | nil => simp [leafSumsFrom, wsumFrom, Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hw]
  | cons v vs ih =>
    simp only [leafSumsFrom, wrapAdd, wrapMul]
    rw [ih (i + 1) _ _ (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))]
    simp only [List.sum_cons, wsumFrom, Prod.mk.injEq]
    constructor <;> omega

/-- `any |= v` over the leaf. -/
def orFrom : List Nat → Nat → Nat
  | [], a => a
  | v :: vs, a => orFrom vs (a ||| v)

/-- `leaf_sums_scalar` (src/lib.rs:2090-2100): `(qty, weighted, any)`. -/
def leafSumsFast (vals : List Nat) : Nat × Nat × Nat :=
  ((leafSumsFrom 0 vals 0 0).1, (leafSumsFrom 0 vals 0 0).2, orFrom vals 0)

/-- `LEAF_SUM_EXACT_BOUND` (src/lib.rs:2084). -/
def LEAF_SUM_EXACT_BOUND : Nat := 2 ^ 52

/-- `leaf_sums_wide` (src/lib.rs:2107-2116): exact sums in `u128`;
`u64::try_from(qty).ok()?` and `u64::try_from(weighted).unwrap_or(u64::MAX)`. -/
def leafSumsWide (vals : List Nat) : Option (Nat × Nat) :=
  if vals.sum ≤ U64_MAX then some (vals.sum, sat (wsumFrom 0 vals)) else none

/-- `Glass::leaf_sums` (src/lib.rs:1074-1088). -/
def leafSums (vals : List Nat) : Option (Nat × Nat) :=
  let r := leafSumsFast vals
  if r.2.2 < LEAF_SUM_EXACT_BOUND then some (r.1, r.2.1) else leafSumsWide vals

/-- The OR-reduction guard: the OR of the quantities is below `2^n` only if
every quantity is. -/
theorem orFrom_lt {n : Nat} : ∀ (vs : List Nat) (a : Nat), orFrom vs a < 2 ^ n →
    a < 2 ^ n ∧ ∀ v ∈ vs, v < 2 ^ n
  | [], a, h => ⟨h, by simp⟩
  | v :: vs, a, h => by
    obtain ⟨h1, h2⟩ := orFrom_lt vs (a ||| v) h
    have ha : a ≤ a ||| v := Nat.left_le_or
    have hv : v ≤ a ||| v := Nat.right_le_or
    refine ⟨by omega, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · exact h2 x hx

/-- ... and conversely (so the guard is exactly "every quantity < 2^n"). -/
theorem orFrom_lt_of {n : Nat} : ∀ (vs : List Nat) (a : Nat), a < 2 ^ n →
    (∀ v ∈ vs, v < 2 ^ n) → orFrom vs a < 2 ^ n
  | [], _, ha, _ => ha
  | v :: vs, a, ha, hv => by
    refine orFrom_lt_of vs _ (Nat.or_lt_two_pow ha (hv v (by simp))) (fun x hx => hv x (by simp [hx]))

theorem sum_le_of_le {C : Nat} : ∀ (vs : List Nat), (∀ v ∈ vs, v ≤ C) → vs.sum ≤ vs.length * C
  | [], _ => by simp
  | v :: vs, h => by
    have := sum_le_of_le vs (fun x hx => h x (by simp [hx]))
    have := h v (by simp)
    simp only [List.sum_cons, List.length_cons, Nat.succ_mul]; omega

theorem wsum_le_of_le {C K : Nat} : ∀ (i : Nat) (vs : List Nat), (∀ v ∈ vs, v ≤ C) →
    i + vs.length ≤ K → wsumFrom i vs ≤ vs.length * (K * C)
  | _, [], _, _ => by simp [wsumFrom]
  | i, v :: vs, h, hk => by
    simp only [List.length_cons] at hk
    have ih := wsum_le_of_le (C := C) (K := K) (i + 1) vs (fun x hx => h x (by simp [hx])) (by omega)
    have hiv : i * v ≤ K * C := Nat.mul_le_mul (show i ≤ K by omega) (h v (by simp))
    simp only [wsumFrom, List.length_cons, Nat.succ_mul]; omega

/-- **`leaf_sums` is exact.** For a leaf of at most 64 slots it returns the
exact quantity sum and the saturated slot-weighted sum, or `none` exactly when
the quantity sum does not fit in `u64`. No precondition on the quantities. -/
theorem leafSums_spec (vals : List Nat) (hlen : vals.length ≤ 64) :
    leafSums vals =
      if vals.sum ≤ U64_MAX then some (vals.sum, sat (wsumFrom 0 vals)) else none := by
  unfold leafSums
  simp only [leafSumsFast]
  split
  · rename_i hg
    obtain ⟨_, hall⟩ := orFrom_lt (n := 52) vals 0 hg
    have hC : ∀ v ∈ vals, v ≤ 2 ^ 52 - 1 := fun v hv => by have := hall v hv; omega
    have hs := sum_le_of_le vals hC
    have hw := wsum_le_of_le (K := 64) 0 vals hC (by omega)
    have hs' : vals.sum < 2 ^ 64 := by
      have : vals.length * (2 ^ 52 - 1) ≤ 64 * (2 ^ 52 - 1) := Nat.mul_le_mul_right _ hlen
      omega
    have hw' : wsumFrom 0 vals < 2 ^ 64 := by
      have : vals.length * (64 * (2 ^ 52 - 1)) ≤ 64 * (64 * (2 ^ 52 - 1)) :=
        Nat.mul_le_mul_right _ hlen
      omega
    rw [leafSumsFrom_eq 0 vals 0 0 (by decide) (by decide)]
    have h1 : vals.sum ≤ U64_MAX := by unfold U64_MAX; omega
    simp [Nat.mod_eq_of_lt hs', Nat.mod_eq_of_lt hw', h1,
      sat_of_le (show wsumFrom 0 vals ≤ U64_MAX by unfold U64_MAX; omega)]
  · rfl

/-- The branch condition `if let Some((qty_total, weighted)) = self.leaf_sums(..)
&& qty_total <= shares` (src/lib.rs:1164, 1347, 1458, 1543), parameterised by
the `leaf_sums` implementation `S`. -/
def fits (S : List Nat → Option (Nat × Nat)) (vals : List Nat) (s : Nat) : Option (Nat × Nat) :=
  match S vals with
  | some (q, w) => if q ≤ s then some (q, w) else none
  | none => none

/-- With the fixed `leaf_sums` and a `u64` order size, the whole-leaf branch
is taken exactly when the leaf's true quantity fits in the order. -/
theorem fits_leafSums (vals : List Nat) (hlen : vals.length ≤ 64) {s : Nat} (hs : s ≤ U64_MAX) :
    fits leafSums vals s =
      if vals.sum ≤ s then some (vals.sum, sat (wsumFrom 0 vals)) else none := by
  unfold fits; rw [leafSums_spec vals hlen]
  by_cases h1 : vals.sum ≤ U64_MAX
  · simp [h1]
  · have : ¬ vals.sum ≤ s := by omega
    simp [h1, this]

/-! ## Leaves -/

/-- A trie leaf: partial key `ht_k` and the 64 dense quantities. -/
structure Leaf where
  pkey : Nat
  vals : List Nat
  deriving DecidableEq, Repr

/-- `(leaf.ht_k as u64) << BITS_PER_LEVEL`. -/
def base (L : Leaf) : Nat := L.pkey * 64

def cells (L : Leaf) : List Level := cellsFrom (base L) 0 L.vals

/-- The price levels a leaf holds, ascending. -/
def levelsOf (L : Leaf) : List Level := nz (cells L)

/-- A leaf as the crate builds it. The correctness theorems need only
`vals.length ≤ 64`; `WF` documents the representation and certifies that the
regression books are reachable. -/
structure Leaf.WF (L : Leaf) : Prop where
  pkey_lt : L.pkey < 2 ^ 26
  len : L.vals.length = 64
  vals_lt : ∀ v ∈ L.vals, v < 2 ^ 64
  nonempty : ∃ v ∈ L.vals, v ≠ 0

/-- The precondition of the whole-leaf fast path: neither of the two sums
`leaf_sums` computes wraps. -/

theorem nz_cells (L : Leaf) : nz (cells L) = levelsOf L := rfl

theorem qty_levelsOf (L : Leaf) : qty (levelsOf L) = L.vals.sum := qty_cells _ _ _

theorem cost_levelsOf (L : Leaf) :
    cost (levelsOf L) = base L * L.vals.sum + wsumFrom 0 L.vals := cost_cells _ _ _

/-- The book held by a leaf list, each leaf's levels in walk direction `d`. -/
def flatO (d : Bool) : List Leaf → List Level
  | [] => []
  | L :: ls => orient d (levelsOf L) ++ flatO d ls

/-- The ascending book held by the glass tier. -/
abbrev flat : List Leaf → List Level := flatO false

theorem flatO_append (d : Bool) (a b : List Leaf) : flatO d (a ++ b) = flatO d a ++ flatO d b := by
  induction a with
  | nil => rfl
  | cons L a ih => simp [flatO, ih]

/-- Walking the leaf list backward with each leaf's slots descending visits
the ascending book in reverse. -/
theorem flatO_true_reverse (ls : List Leaf) : flatO true ls.reverse = (flat ls).reverse := by
  induction ls with
  | nil => rfl
  | cons L ls ih => simp [flatO, flatO_append, ih, orient]

/-! ## Per-slot loops -/

/-- Saturating accumulation of one term. -/
theorem acc_step (x p b : Nat) : satAdd (sat x) (satMul p b) = sat (x + p * b) :=
  satAdd_sat_sat x (p * b)

/-- Saturating accumulation of a whole leaf. -/
theorem acc_whole (x b q w : Nat) :
    satAdd (satAdd (sat x) (satMul b q)) w = sat (x + (b * q + w)) := by
  rw [acc_step, satAdd_sat, Nat.add_assoc]

/-- A whole leaf charged with its *saturated* weighted sum (what `leaf_sums`
now returns) still accumulates the exact cost, saturated. -/
theorem acc_whole_sat (x b q w : Nat) :
    satAdd (satAdd (sat x) (satMul b q)) (sat w) = sat (x + (b * q + w)) := by
  rw [acc_step, satAdd_sat_sat, Nat.add_assoc]

/-- The read-only per-slot scan of `compute_buy_cost` (src/lib.rs:1361-1376)
and `compute_sell_cost` (src/lib.rs:1557-1569), over occupied cells in walk
order. Returns `(total, target)`; the Rust early `return` when the target
hits 0 is the `(total, 0)` exit (everything after it is skipped once the
target is 0). -/
def scan : List Level → Nat → Nat → Nat × Nat
  | [], total, t => (total, t)
  | (p, v) :: cs, total, t =>
    if v = 0 then scan cs total t          -- mask bit clear: slot not visited
    else
      let buy := min v t                   -- qty.min(target_shares)
      let total := satAdd total (satMul p buy)
      let t := t - buy
      if t = 0 then (total, 0)             -- `return total_cost`
      else scan cs total t                 -- `mask = clear_lowest_bit(mask)`

theorem scan_spec (cs : List Level) (x t : Nat) :
    scan cs (sat x) t = (sat (x + (buySpec (nz cs) t).1), (buySpec (nz cs) t).2.1) := by
  induction cs generalizing x t with
  | nil => simp [scan, nz, buySpec]
  | cons hd cs ih =>
    obtain ⟨p, v⟩ := hd
    by_cases hv : v = 0
    · simp [scan, nz, hv, ih]
    · by_cases ht : t = 0
      · subst ht; simp [scan, nz, hv, acc_step, buySpec_zero]
      · by_cases hvt : v ≤ t
        · have hmin : min v t = v := Nat.min_eq_left hvt
          by_cases hrest : t - v = 0
          · simp [scan, nz, hv, hmin, hrest, acc_step, buySpec, ht, hvt, buySpec_zero]
          · simp [scan, nz, hv, hmin, hrest, acc_step, buySpec, ht, hvt, ih, Nat.add_assoc]
        · have hmin : min v t = t := Nat.min_eq_right (by omega)
          simp [scan, nz, hv, hmin, acc_step, buySpec, ht, hvt]

/-- The mutating partial-leaf walk of `buy_shares` (src/lib.rs:1176-1205) and
`sell_shares` (src/lib.rs:1469-1497), over cells in walk order. Returns
`(total, shares left, updated cells)`. -/
def consume : List Level → Nat → Nat → Nat × Nat × List Level
  | [], total, s => (total, s, [])
  | (p, v) :: cs, total, s =>
    if s = 0 then (total, s, (p, v) :: cs)             -- `while shares > 0` exits
    else if v = 0 then                                  -- mask bit clear: skipped
      let r := consume cs total s
      (r.1, r.2.1, (p, v) :: r.2.2)
    else if v ≤ s then                                  -- level fully taken
      let r := consume cs (satAdd total (satMul p v)) (s - v)
      (r.1, r.2.1, (p, 0) :: r.2.2)                     -- `values[slot] = 0`
    else                                                -- level partially taken
      (satAdd total (satMul p s), 0, (p, v - s) :: cs)  -- `values[slot] -= shares`

theorem consume_spec (cs : List Level) (x s : Nat) :
    (consume cs (sat x) s).1 = sat (x + (buySpec (nz cs) s).1) ∧
    (consume cs (sat x) s).2.1 = (buySpec (nz cs) s).2.1 ∧
    nz (consume cs (sat x) s).2.2 = (buySpec (nz cs) s).2.2 ∧
    (consume cs (sat x) s).2.2.map Prod.fst = cs.map Prod.fst := by
  induction cs generalizing x s with
  | nil => simp [consume, nz, buySpec]
  | cons hd cs ih =>
    obtain ⟨p, v⟩ := hd
    by_cases hs : s = 0
    · subst hs; simp [consume, buySpec_zero]
    · by_cases hv : v = 0
      · subst hv
        obtain ⟨h1, h2, h3, h4⟩ := ih x s
        simp [consume, nz, hs, h1, h2, h3, h4]
      · by_cases hvs : v ≤ s
        · obtain ⟨h1, h2, h3, h4⟩ := ih (x + p * v) (s - v)
          simp [consume, nz, hs, hv, hvs, acc_step, h1, h2, h3, h4, buySpec, Nat.add_assoc]
        · have hpos : v - s ≠ 0 := by omega
          simp [consume, nz, hs, hv, hvs, acc_step, buySpec, hpos]


/-! ## `buy_shares` / `sell_shares`: the glass sweep -/

/-- The glass-tier loop of `buy_shares` (`d = false`, src/lib.rs:1128-1210)
and `sell_shares` (`d = true`, src/lib.rs:1445-1500), over the leaf list in
walk order (buy: from `min_leaf` along `next_leaf`; sell: from `max_leaf`
along `prev_leaf`), with `leaf_sums` implementation `S`. Returns
`(total, shares left, remaining leaves)`. In the partial walk, running out of
cells (`consume`'s `[]` case) is the new `m == 0` / `leaf.mask == 0` guard,
which breaks out; the proof shows it is never reached with the fixed `S`. -/
def sweep (S : List Nat → Option (Nat × Nat)) (d : Bool) :
    List Leaf → Nat → Nat → Nat × Nat × List Leaf
  | [], s, total => (total, s, [])                -- glass exhausted
  | L :: rest, s, total =>
    if s = 0 then (total, s, L :: rest)           -- `while shares > 0` exits
    else
      match fits S L.vals s with
      | some (q, w) =>
        -- consume the entire leaf (`remove_min_leaf` / `remove_max_leaf`)
        sweep S d rest (s - q) (satAdd (satAdd total (satMul (base L) q)) w)
      | none =>
        -- partial: walk set bits from the cheapest (buy) / dearest (sell) slot
        let r := consume (orient d (cells L)) total s
        (r.1, r.2.1, { L with vals := (orient d r.2.2).map Prod.snd } :: rest)

theorem sweep_spec (d : Bool) (ls : List Leaf) (hlen : ∀ L ∈ ls, L.vals.length ≤ 64)
    (s x : Nat) (hs : s ≤ U64_MAX) :
    (sweep leafSums d ls s (sat x)).1 = sat (x + (buySpec (flatO d ls) s).1) ∧
    (sweep leafSums d ls s (sat x)).2.1 = (buySpec (flatO d ls) s).2.1 ∧
    flatO d (sweep leafSums d ls s (sat x)).2.2 = (buySpec (flatO d ls) s).2.2 := by
  induction ls generalizing s x with
  | nil => simp [sweep, flatO, buySpec]
  | cons L rest ih =>
    have hL := hlen L (by simp)
    have hrest : ∀ L ∈ rest, L.vals.length ≤ 64 := fun L' h => hlen L' (by simp [h])
    by_cases hs0 : s = 0
    · subst hs0; simp [sweep, buySpec_zero]
    · have hq_or := qty_orient d (levelsOf L)
      rw [qty_levelsOf] at hq_or
      by_cases hq : L.vals.sum ≤ s
      · -- whole leaf
        have hf : fits leafSums L.vals s = some (L.vals.sum, sat (wsumFrom 0 L.vals)) := by
          rw [fits_leafSums L.vals hL hs]; simp [hq]
        have hall : buySpec (orient d (levelsOf L)) s =
            (cost (levelsOf L), s - L.vals.sum, []) := by
          rw [buySpec_all (orient d (levelsOf L)) _
            (fun lv h => nz_pos (cells L) lv (mem_orient.mp h)) (by omega), cost_orient, hq_or]
        obtain ⟨h1, h2, h3⟩ := ih hrest (s - L.vals.sum) (x + cost (levelsOf L)) (by omega)
        simp only [sweep, hs0, hf, if_false, flatO, buySpec_append, hall,
          acc_whole_sat, ← cost_levelsOf]
        refine ⟨?_, h2, ?_⟩
        · rw [h1, Nat.add_assoc]
        · simpa using h3
      · -- partial leaf
        have hf : fits leafSums L.vals s = none := by
          rw [fits_leafSums L.vals hL hs]; simp [hq]
        have hshort : (buySpec (orient d (levelsOf L)) s).2.1 = 0 :=
          buySpec_short _ _ (by omega)
        obtain ⟨c1, c2, c3, c4⟩ := consume_spec (orient d (cells L)) x s
        rw [nz_orient, nz_cells] at c1 c2 c3
        simp only [sweep, hs0, hf, if_false, flatO, buySpec_append, hshort,
          buySpec_zero]
        generalize consume (orient d (cells L)) (sat x) s = r at c1 c2 c3 c4 ⊢
        -- the rebuilt leaf holds exactly the partially consumed cells
        have hcells : cells { L with vals := (orient d r.2.2).map Prod.snd } =
            orient d r.2.2 := by
          apply cells_rebuild
          rw [map_orient, c4, map_orient, orient_orient]
          rfl
        refine ⟨by simpa using c1, by rw [c2, hshort], ?_⟩
        simp only [levelsOf, hcells, nz_orient, orient_orient, c3]

/-- The partial walk never hits the `m == 0` guard: with the fixed
`leaf_sums`, the partial branch leaves no shares unfilled inside the leaf. -/
theorem sweep_partial_fills (d : Bool) (L : Leaf) (s x : Nat)
    (hL : L.vals.length ≤ 64) (hs : s ≤ U64_MAX)
    (hf : fits leafSums L.vals s = none) :
    (consume (orient d (cells L)) (sat x) s).2.1 = 0 := by
  rw [fits_leafSums L.vals hL hs] at hf
  have hq : ¬ L.vals.sum ≤ s := by intro h; simp [h] at hf
  obtain ⟨_, c2, _, _⟩ := consume_spec (orient d (cells L)) x s
  rw [nz_orient, nz_cells] at c2
  rw [c2]; apply buySpec_short
  rw [qty_orient, qty_levelsOf]; omega

/-- `buy_shares`'s glass loop. -/
abbrev buyKernel (ls : List Leaf) (s : Nat) : Nat × Nat × List Leaf :=
  sweep leafSums false ls s 0

/-- `sell_shares`'s glass loop; the leaf list is walked from its max leaf and
the remaining leaves come back in that (descending) order. -/
abbrev sellKernel (ls : List Leaf) (s : Nat) : Nat × Nat × List Leaf :=
  sweep leafSums true ls.reverse s 0

/-- **`buy_shares` (glass tier) is correct:** for any leaves of ≤ 64 slots and
any `u64` order size it charges `min(exact greedy cost, u64::MAX)`, reports
the spec's unfilled shares, and leaves exactly the spec's remaining levels. -/
theorem buyKernel_correct (ls : List Leaf) (hlen : ∀ L ∈ ls, L.vals.length ≤ 64) (s : Nat)
    (hs : s ≤ U64_MAX) :
    (buyKernel ls s).1 = sat (buySpec (flat ls) s).1 ∧
    (buyKernel ls s).2.1 = (buySpec (flat ls) s).2.1 ∧
    flat (buyKernel ls s).2.2 = (buySpec (flat ls) s).2.2 := by
  have h := sweep_spec false ls hlen s 0 hs
  simp only [sat_of_le (show 0 ≤ U64_MAX by decide), Nat.zero_add] at h
  exact h

/-- **`sell_shares` (glass tier) is correct**, against the greedy-from-the-top
spec; remaining leaves (re-ascended) hold exactly the spec's remaining
levels. -/
theorem sellKernel_correct (ls : List Leaf) (hlen : ∀ L ∈ ls, L.vals.length ≤ 64) (s : Nat)
    (hs : s ≤ U64_MAX) :
    (sellKernel ls s).1 = sat (sellSpec (flat ls) s).1 ∧
    (sellKernel ls s).2.1 = (sellSpec (flat ls) s).2.1 ∧
    flat (sellKernel ls s).2.2.reverse = (sellSpec (flat ls) s).2.2 := by
  have h := sweep_spec true ls.reverse (fun L hL => hlen L (List.mem_reverse.mp hL)) s 0 hs
  simp only [sat_of_le (show 0 ≤ U64_MAX by decide), Nat.zero_add,
    flatO_true_reverse] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  have hr := flatO_true_reverse (sellKernel ls s).2.2.reverse
  rw [List.reverse_reverse] at hr
  simp only [sellSpec, ← h3, hr, List.reverse_reverse]

/-! ## `compute_buy_cost` / `compute_sell_cost` -/

/-- The glass-tier loop shared by `compute_buy_cost` (`d = false`,
src/lib.rs:1337-1377) and `compute_sell_cost` (`d = true`,
src/lib.rs:1533-1571): the first leaf is scanned per slot; later leaves are
charged whole when `leaf_sums` (implementation `S`) says they fit in the
target, else scanned. -/
def computeLeaves (S : List Nat → Option (Nat × Nat)) (d : Bool) :
    List Leaf → Bool → Nat → Nat → Nat × Nat
  | [], _, total, t => (total, t)                         -- `curr_leaf_idx == u32::MAX`
  | L :: rest, first, total, t =>
    if t = 0 then (total, t)                              -- `target_shares > 0` fails
    else
      match (if first then none else fits S L.vals t) with  -- `if !first { if let Some(..) && .. }`
      | some (q, w) =>
        computeLeaves S d rest false (satAdd (satAdd total (satMul (base L) q)) w) (t - q)
      | none =>                                           -- `first = false; while mask != 0`
        let r := scan (orient d (cells L)) total t
        if r.2 = 0 then (r.1, 0)                          -- early `return`
        else computeLeaves S d rest false r.1 r.2

theorem computeLeaves_spec (d : Bool) (ls : List Leaf) (hlen : ∀ L ∈ ls, L.vals.length ≤ 64)
    (first : Bool) (x t : Nat) (ht : t ≤ U64_MAX) :
    computeLeaves leafSums d ls first (sat x) t =
      (sat (x + (buySpec (flatO d ls) t).1), (buySpec (flatO d ls) t).2.1) := by
  induction ls generalizing first x t with
  | nil => simp [computeLeaves, flatO, buySpec]
  | cons L rest ih =>
    have hL := hlen L (by simp)
    have hrest : ∀ L ∈ rest, L.vals.length ≤ 64 := fun L' h => hlen L' (by simp [h])
    by_cases ht0 : t = 0
    · subst ht0; simp [computeLeaves, buySpec_zero]
    · have hq_or := qty_orient d (levelsOf L)
      rw [qty_levelsOf] at hq_or
      have hfits := fits_leafSums L.vals hL ht
      by_cases hc : first = false ∧ L.vals.sum ≤ t
      · obtain ⟨hfirst, hq⟩ := hc
        subst hfirst
        have hall : buySpec (orient d (levelsOf L)) t =
            (cost (levelsOf L), t - L.vals.sum, []) := by
          rw [buySpec_all (orient d (levelsOf L)) _
            (fun lv h => nz_pos (cells L) lv (mem_orient.mp h)) (by omega), cost_orient, hq_or]
        simp only [computeLeaves, ht0, hfits, hq, if_false, if_true, Bool.false_eq_true,
          flatO, buySpec_append, hall, acc_whole_sat, ← cost_levelsOf,
          ih hrest false (x + cost (levelsOf L)) (t - L.vals.sum) (by omega), Nat.add_assoc]
      · have hnone : (if first = true then none else fits leafSums L.vals t) = none := by
          cases first
          · simp only [Bool.false_eq_true, if_false, hfits]
            have : ¬ L.vals.sum ≤ t := fun h => hc ⟨rfl, h⟩
            simp [this]
          · rfl
        have hs := scan_spec (orient d (cells L)) x t
        rw [nz_orient] at hs
        simp only [computeLeaves, ht0, if_false, hnone, hs, flatO, buySpec_append]
        by_cases h0 : (buySpec (orient d (levelsOf L)) t).2.1 = 0
        · simp [nz_cells, h0, buySpec_zero]
        · have hle : (buySpec (orient d (levelsOf L)) t).2.1 ≤ t := buySpec_unfilled_le _ _
          simp only [nz_cells, h0, if_false]
          rw [ih hrest false _ _ (by omega)]
          simp [Nat.add_assoc]



/-- `compute_buy_cost`'s preempt tail (src/lib.rs:1379-1394): the overflow
tier's sorted keys, ascending, one level at a time. -/
def preemptAsc : List Level → Nat → Nat → Nat
  | [], total, _ => total
  | (k, avail) :: rest, total, t =>
    if t = 0 then total                                   -- `if target_shares == 0 break`
    else preemptAsc rest (satAdd total (satMul k (min avail t))) (t - min avail t)

theorem preemptAsc_spec (l : List Level) (x t : Nat) :
    preemptAsc l (sat x) t = sat (x + (buySpec l t).1) := by
  induction l generalizing x t with
  | nil => simp [preemptAsc, buySpec]
  | cons hd l ih =>
    obtain ⟨k, a⟩ := hd
    by_cases ht : t = 0
    · subst ht; simp [preemptAsc, buySpec]
    · by_cases hat : a ≤ t
      · simp [preemptAsc, buySpec, ht, hat, Nat.min_eq_left hat, acc_step, ih, Nat.add_assoc]
      · have hmin : min a t = t := Nat.min_eq_right (by omega)
        simp [preemptAsc, buySpec, ht, hat, hmin, acc_step, ih, buySpec_zero]

/-- `compute_buy_cost` with `leaf_sums` implementation `S`: glass leaves
ascending, then the overflow tier's levels (`preempt`, ascending by key —
`sorted_preempt_keys`; src/lib.rs:1379-1394). -/
def computeBuyCostWith (S : List Nat → Option (Nat × Nat)) (glass : List Leaf)
    (preempt : List Level) (target : Nat) : Nat :=
  let r := computeLeaves S false glass true 0 target
  if 0 < r.2 then preemptAsc preempt r.1 r.2 else r.1

/-- `compute_buy_cost` (src/lib.rs:1335-1395). -/
abbrev computeBuyCost := computeBuyCostWith leafSums

/-- **`compute_buy_cost` is correct:** for leaves of ≤ 64 slots and a `u64`
target it returns `min(exact greedy cost over glass-then-preempt levels,
u64::MAX)`. With the tier invariant (glass prices < preempt prices) that list
is the whole book in ascending order. -/
theorem computeBuyCost_correct (glass : List Leaf) (preempt : List Level)
    (hlen : ∀ L ∈ glass, L.vals.length ≤ 64) (n : Nat) (hn : n ≤ U64_MAX) :
    computeBuyCost glass preempt n = sat (buySpec (flat glass ++ preempt) n).1 := by
  have h := computeLeaves_spec false glass hlen true 0 n hn
  rw [sat_of_le (show 0 ≤ U64_MAX by decide), Nat.zero_add] at h
  simp only [computeBuyCost, computeBuyCostWith, h, buySpec_append]
  by_cases h0 : (buySpec (flat glass) n).2.1 = 0
  · simp [h0, buySpec_zero]
  · simp [Nat.pos_of_ne_zero h0, preemptAsc_spec]

/-- `compute_sell_cost`'s preempt head (src/lib.rs:1514-1530): the overflow
tier's sorted keys, descending (`keys.iter().rev()`). -/

def preemptDesc : List Level → Nat → Nat → Nat × Nat
  | [], total, t => (total, t)
  | (k, avail) :: rest, total, t =>
    if t = 0 then (total, 0)                              -- `return total_proceeds`
    else preemptDesc rest (satAdd total (satMul k (min avail t))) (t - min avail t)

theorem preemptDesc_spec (l : List Level) (x t : Nat) :
    preemptDesc l (sat x) t = (sat (x + (buySpec l t).1), (buySpec l t).2.1) := by
  induction l generalizing x t with
  | nil => simp [preemptDesc, buySpec]
  | cons hd l ih =>
    obtain ⟨k, a⟩ := hd
    by_cases ht : t = 0
    · subst ht; simp [preemptDesc, buySpec]
    · by_cases hat : a ≤ t
      · simp [preemptDesc, buySpec, ht, hat, Nat.min_eq_left hat, acc_step, ih, Nat.add_assoc]
      · have hmin : min a t = t := Nat.min_eq_right (by omega)
        have hz : preemptDesc l (sat (x + k * t)) 0 = (sat (x + k * t), 0) := by
          cases l with
          | nil => rfl
          | cons hd _ => obtain ⟨_, _⟩ := hd; simp [preemptDesc]
        simp [preemptDesc, buySpec, ht, hat, hmin, acc_step, hz]

/-- `compute_sell_cost` with `leaf_sums` implementation `S`: the overflow
tier first (it holds the highest prices), descending, then glass leaves from
the max leaf backward. -/
def computeSellCostWith (S : List Nat → Option (Nat × Nat)) (glass : List Leaf)
    (preempt : List Level) (target : Nat) : Nat :=
  let r := preemptDesc preempt.reverse 0 target
  (computeLeaves S true glass.reverse true r.1 r.2).1

/-- `compute_sell_cost` (src/lib.rs:1510-1572). -/
abbrev computeSellCost := computeSellCostWith leafSums

/-- **`compute_sell_cost` is correct:** it returns `min(exact
greedy-from-the-top proceeds over the ascending book glass ++ preempt,
u64::MAX)`. -/
theorem computeSellCost_correct (glass : List Leaf) (preempt : List Level)
    (hlen : ∀ L ∈ glass, L.vals.length ≤ 64) (n : Nat) (hn : n ≤ U64_MAX) :
    computeSellCost glass preempt n = sat (sellSpec (flat glass ++ preempt) n).1 := by
  have hp := preemptDesc_spec preempt.reverse 0 n
  rw [sat_of_le (show 0 ≤ U64_MAX by decide), Nat.zero_add] at hp
  have hle : (buySpec preempt.reverse n).2.1 ≤ U64_MAX :=
    Nat.le_trans (buySpec_unfilled_le _ _) hn
  have hg := computeLeaves_spec true glass.reverse
    (fun L hL => hlen L (List.mem_reverse.mp hL)) true
    (buySpec preempt.reverse n).1 (buySpec preempt.reverse n).2.1 hle
  simp only [computeSellCost, computeSellCostWith, hp, hg, sellSpec, List.reverse_append,
    buySpec_append, flatO_true_reverse]


/-! ## The whole book is ascending

`buySpec` is greedy from the *front*; these lemmas show the front is the
cheapest level, so the spec above really is "buy from the lowest price". -/

theorem cellsFrom_price_bounds (b i : Nat) (vs : List Nat) :
    ∀ lv ∈ cellsFrom b i vs, b + i ≤ lv.1 ∧ lv.1 < b + i + vs.length := by
  induction vs generalizing i with
  | nil => simp [cellsFrom]
  | cons v vs ih =>
    intro lv hlv
    simp only [cellsFrom, List.mem_cons] at hlv
    rcases hlv with rfl | hlv
    · simp
    · have := ih (i + 1) lv hlv; simp only [List.length_cons]; omega

theorem mem_nz {lv : Level} {c : List Level} (h : lv ∈ nz c) : lv ∈ c := by
  induction c with
  | nil => simp [nz] at h
  | cons hd c ih =>
    obtain ⟨p, v⟩ := hd
    by_cases hv : v = 0
    · simp only [nz, hv, if_true] at h; exact List.mem_cons_of_mem _ (ih h)
    · simp only [nz, hv, if_false, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

theorem ascending_cellsFrom (b i : Nat) (vs : List Nat) : Ascending (nz (cellsFrom b i vs)) := by
  induction vs generalizing i with
  | nil => trivial
  | cons v vs ih =>
    by_cases hv : v = 0
    · simp only [cellsFrom, nz, hv, if_true]; exact ih (i + 1)
    · simp only [cellsFrom, nz, hv, if_false, Ascending]
      refine ⟨fun lv hlv => ?_, ih (i + 1)⟩
      have := cellsFrom_price_bounds b (i + 1) vs lv (mem_nz hlv)
      omega

theorem ascending_append {a b : List Level} (ha : Ascending a) (hb : Ascending b)
    (hab : ∀ x ∈ a, ∀ y ∈ b, x.1 < y.1) : Ascending (a ++ b) := by
  induction a with
  | nil => simpa using hb
  | cons hd a ih =>
    obtain ⟨p, q⟩ := hd
    simp only [Ascending] at ha
    simp only [List.cons_append, Ascending, List.mem_append]
    refine ⟨fun lv hlv => ?_, ih ha.2 (fun x hx y hy => hab x (List.mem_cons_of_mem _ hx) y hy)⟩
    rcases hlv with hlv | hlv
    · exact ha.1 lv hlv
    · exact hab (p, q) List.mem_cons_self lv hlv

/-- Leaves with strictly increasing partial keys and ≤ 64 slots each hold an
ascending book (the linked leaf list is in key order). -/
def KeyOrdered : List Leaf → Prop
  | [] => True
  | L :: ls => (∀ L' ∈ ls, L.pkey < L'.pkey) ∧ KeyOrdered ls

theorem flat_ascending (ls : List Leaf) (hk : KeyOrdered ls)
    (hlen : ∀ L ∈ ls, L.vals.length ≤ 64) : Ascending (flat ls) := by
  induction ls with
  | nil => trivial
  | cons L ls ih =>
    simp only [KeyOrdered] at hk
    simp only [flat, flatO, orient, Bool.false_eq_true, if_false]
    refine ascending_append (ascending_cellsFrom _ _ _)
      (ih hk.2 (fun L' h => hlen L' (List.mem_cons_of_mem _ h))) ?_
    intro x hx y hy
    have hx' := cellsFrom_price_bounds _ _ _ x (mem_nz hx)
    have hlenL := hlen L List.mem_cons_self
    -- y lies in some later leaf L'
    have : ∃ L' ∈ ls, y ∈ levelsOf L' := by
      clear ih hk hlen hx hx'
      induction ls with
      | nil => simp [flatO] at hy
      | cons L' ls ih' =>
        simp only [flatO, orient, Bool.false_eq_true, if_false, List.mem_append] at hy
        rcases hy with hy | hy
        · exact ⟨L', List.mem_cons_self, hy⟩
        · obtain ⟨L'', h1, h2⟩ := ih' hy; exact ⟨L'', List.mem_cons_of_mem _ h1, h2⟩
    obtain ⟨L', hL', hyL'⟩ := this
    have hy' := cellsFrom_price_bounds _ _ _ y (mem_nz hyL')
    have hlt := hk.1 L' hL'
    simp only [base] at hx' hy'
    have : L.pkey * 64 + 64 ≤ L'.pkey * 64 := by omega
    omega


/-! ## Regression: the overflow books are now handled exactly

The three books that broke the old `leaf_sums` (see *Legacy* below), run
through the fixed model. -/

def cexLeaf0 : Leaf := ⟨0, List.replicate 10 0 ++ [5] ++ List.replicate 53 0⟩
def cexLeaf1 : Leaf := ⟨1, [2 ^ 63, 2 ^ 63] ++ List.replicate 62 0⟩
/-- Buy-side book `{10: 5, 64: 2^63, 65: 2^63}`. -/
def cexGlass : List Leaf := [cexLeaf0, cexLeaf1]

def sellLeaf0 : Leaf := ⟨0, List.replicate 10 0 ++ [2 ^ 63, 2 ^ 63] ++ List.replicate 52 0⟩
def sellLeaf1 : Leaf := ⟨1, List.replicate 36 0 ++ [5] ++ List.replicate 27 0⟩
/-- Sell-side book `{10: 2^63, 11: 2^63, 100: 5}`. -/
def sellGlass : List Leaf := [sellLeaf0, sellLeaf1]

def cex2Leaf : Leaf := ⟨0, List.replicate 63 0 ++ [2 ^ 59]⟩
/-- `{63: 2^59}`: exact cost 63·2^59 exceeds `u64::MAX`. -/
def cex2Glass : List Leaf := [cex2Leaf]

/-- All three are well-formed crate leaves, in key order. -/
theorem books_wf : cexLeaf0.WF ∧ cexLeaf1.WF ∧ KeyOrdered cexGlass ∧
    sellLeaf0.WF ∧ sellLeaf1.WF ∧ KeyOrdered sellGlass ∧ cex2Leaf.WF := by
  refine ⟨⟨by decide, by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide, by decide⟩,
    by simp [KeyOrdered, cexGlass, cexLeaf0, cexLeaf1],
    ⟨by decide, by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide, by decide⟩,
    by simp [KeyOrdered, sellGlass, sellLeaf0, sellLeaf1],
    ⟨by decide, by decide, by decide, by decide⟩⟩

theorem cex_book : flat cexGlass = [(10, 5), (64, 2 ^ 63), (65, 2 ^ 63)] := by decide
theorem sell_book : flat sellGlass = [(10, 2 ^ 63), (11, 2 ^ 63), (100, 5)] := by decide
theorem cex2_book : flat cex2Glass = [(63, 2 ^ 59)] := by decide

/-- The correct answers. -/
theorem cex_spec : sat (buySpec (flat cexGlass) 10).1 = 370 := by decide
theorem sell_spec : sat (sellSpec (flat sellGlass) 10).1 = 555 := by decide
theorem cex2_spec : sat (buySpec (flat cex2Glass) (2 ^ 59)).1 = U64_MAX := by decide

/-- Buy 10 from `{10: 5, 64: 2^63, 65: 2^63}`: cost 370, and the book keeps
`{64: 2^63 - 5, 65: 2^63}`. -/
theorem fixed_compute_buy : computeBuyCost cexGlass [] 10 = 370 := by decide

set_option maxRecDepth 8192 in
theorem fixed_buy : (buyKernel cexGlass 10).1 = 370 ∧ (buyKernel cexGlass 10).2.1 = 0 ∧
    flat (buyKernel cexGlass 10).2.2 = [(64, 2 ^ 63 - 5), (65, 2 ^ 63)] := by decide

/-- Sell 10 into `{10: 2^63, 11: 2^63, 100: 5}`: proceeds 555, and the book
keeps `{10: 2^63, 11: 2^63 - 5}`. -/
theorem fixed_compute_sell : computeSellCost sellGlass [] 10 = 555 := by decide

set_option maxRecDepth 8192 in
theorem fixed_sell : (sellKernel sellGlass 10).1 = 555 ∧ (sellKernel sellGlass 10).2.1 = 0 ∧
    flat (sellKernel sellGlass 10).2.2.reverse = [(10, 2 ^ 63), (11, 2 ^ 63 - 5)] := by decide

/-- Buy 2^59 of `{63: 2^59}`: the cost saturates to `u64::MAX` on both paths
and the level is gone. -/
theorem fixed_compute_buy2 : computeBuyCost cex2Glass [] (2 ^ 59) = U64_MAX := by decide

set_option maxRecDepth 8192 in
theorem fixed_buy2 : (buyKernel cex2Glass (2 ^ 59)).1 = U64_MAX ∧
    flat (buyKernel cex2Glass (2 ^ 59)).2.2 = [] := by decide

/-! ## Legacy: why the fix was needed

Before the fix, `leaf_sums` returned the wrapping sums unconditionally and
the whole-leaf branch tested `qty_total <= shares` on the wrapped value. That
is the same `sweep` / `computeLeaves` with `S := legacySums`. It is correct
only under `NoWrap`; the books above break it, with exactly the numbers the
Rust crate printed before the fix. -/

namespace Legacy

/-- The old `leaf_sums_scalar`: `(Σ qty, Σ slot·qty)`, both mod 2^64. -/
def legacySums (vals : List Nat) : Option (Nat × Nat) := some (leafSumsFrom 0 vals 0 0)

/-- The old whole-leaf precondition: neither sum wraps. -/
def NoWrap (L : Leaf) : Prop := L.vals.sum < 2 ^ 64 ∧ wsumFrom 0 L.vals < 2 ^ 64

abbrev buyKernel (ls : List Leaf) (s : Nat) : Nat × Nat × List Leaf :=
  sweep legacySums false ls s 0
abbrev sellKernel (ls : List Leaf) (s : Nat) : Nat × Nat × List Leaf :=
  sweep legacySums true ls.reverse s 0
abbrev computeBuyCost := computeBuyCostWith legacySums
abbrev computeSellCost := computeSellCostWith legacySums

/-- Old `compute_buy_cost(10)` on `{10: 5, 64: 2^63, 65: 2^63}` returned
9223372036854775858 (correct: 370). -/
theorem cex_compute : computeBuyCost cexGlass [] 10 = 9223372036854775858 := by decide

set_option maxRecDepth 8192 in
/-- Old `buy_shares(10)` charged 9223372036854775858, removed every level, and
believed 5 shares went unfilled. -/
theorem cex_buy : buyKernel cexGlass 10 = (9223372036854775858, 5, []) := by decide

set_option maxRecDepth 8192 in
/-- Old `sell_shares(10)` / `compute_sell_cost(10)` on
`{10: 2^63, 11: 2^63, 100: 5}` returned 9223372036854776308 (correct: 555)
and emptied the book. -/
theorem cex_sell : (sellKernel sellGlass 10).1 = 9223372036854776308 ∧
    (sellKernel sellGlass 10).2.2 = [] ∧
    computeSellCost sellGlass [] 10 = 9223372036854776308 := by decide

/-- There it is the quantity half of `NoWrap` that fails (leaf 1 sums to
exactly 2^64); the slot-weighted half holds. -/
theorem cex_nowrap : ¬ NoWrap cexLeaf1 ∧ cexLeaf1.vals.sum = 2 ^ 64 ∧
    wsumFrom 0 cexLeaf1.vals < 2 ^ 64 ∧ NoWrap cexLeaf0 := by
  have hsum : cexLeaf1.vals.sum = 2 ^ 64 := by decide
  refine ⟨fun h => ?_, hsum, by decide, ⟨by decide, by decide⟩⟩
  have := h.1
  rw [hsum] at this
  exact Nat.lt_irrefl _ this

/-- `{63: 2^59}`: only the slot-weighted half fails. The old
`compute_buy_cost` scanned the first leaf per slot and got `u64::MAX` right;
the old `buy_shares` took the whole-leaf path (`base = 0`, so `base·Q` cannot
saturate) and charged the wrapped 63·2^59 mod 2^64. -/
theorem cex2_nowrap : cex2Leaf.vals.sum < 2 ^ 64 ∧ ¬ wsumFrom 0 cex2Leaf.vals < 2 ^ 64 := by
  refine ⟨by decide, by decide⟩

theorem cex2_compute : computeBuyCost cex2Glass [] (2 ^ 59) = U64_MAX := by decide

set_option maxRecDepth 8192 in
theorem cex2_buy : (buyKernel cex2Glass (2 ^ 59)).1 = 17870283321406128128 := by decide

end Legacy

end Glass.Execution
