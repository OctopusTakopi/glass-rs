import GlassProof.Basic

/-!
# Two-tier routing (trie + preempt tier)

Model of the tier layer of `src/lib.rs`: every public operation routes a key
either to the trie ("glass") or to the overflow `preempt` tier by comparing it
with the threshold `thres`. This is where the July 2026 stale-threshold bug
lived (`tests/differential.rs::thres_stays_correct_after_eviction`).

The preempt tier is the paper's hash table `preempt: AHashMap<u32, u64>` plus
an ordered index of its key set, `preempt_keys: BTreeSet<u32>`, which is
touched only when a level appears or disappears. `thres` is a plain field kept
exact on every key-set change: the lowest index key, or `u32::MAX` (the
paper's "infinity") when the tier is empty.

What is modeled faithfully (each `def` cites the Rust it transcribes):
* `preempt_insert` (a quantity overwrite is one hash write; a new key also
  enters the index and may lower `thres`; the `reserve` call only sizes
  capacity), `preempt_remove`, `refresh_thres`, routing `routes_to_trie`;
* `insert` with eviction of the trie max, `remove`, `update_value` (including
  the transient stored zero), `get`, `min`, `max`, `clear`;
* `refill_if_low` (refill once the trie is `REFILL_BATCH` levels short) and
  the `restructure` loop, which pops the lowest index keys (never the pinned
  `u32::MAX`) into the trie and finally refreshes `thres`.

The `invariant_violated` sites (`preempt_qty` in `min`/`max`, the map lookup
in `restructure`) are modeled as the Rust's non-panicking branch plus a proof
that the panicking branch is unreachable under `Inv`
(`minOp_lookup_present`, `maxOp_lookup_present`, `restructure_never_panics`).

The index is modeled as its ascending element list `idx`; `BTreeSet::insert`
is `sinsert`, `remove` is `List.erase`, `first`/`last`/`pop_first` are
`head?`/`getLast?`/`tail`.

What is abstracted: the trie itself. It is treated as a finite map `G` with
the contract of `glass_insert`/`glass_get(_mut)`/`glass_remove`/`glass_min`/
`glass_max`/`glass_size` (a correct ordered map). Proving the arena trie meets
that contract is a separate obligation; `tests/differential.rs` exercises it.
Ghost state: `gk` lists the trie's key set (`glass_size()` is its length).
-/

namespace Glass.Tiers

abbrev Map := Nat → Option Nat

/-- Point update of a map. -/
def upd (f : Map) (k : Nat) (v : Option Nat) : Map := fun j => if j = k then v else f j

@[simp] theorem upd_self (f : Map) (k : Nat) (v : Option Nat) : upd f k v k = v := by
  simp [upd]

@[simp] theorem upd_ne (f : Map) {j k : Nat} (v : Option Nat) (h : j ≠ k) : upd f k v j = f j := by
  simp [upd, h]

theorem upd_apply (f : Map) (k : Nat) (v : Option Nat) (j : Nat) :
    upd f k v j = if j = k then v else f j := rfl

theorem upd_upd (f : Map) (k : Nat) (a b : Option Nat) : upd (upd f k a) k b = upd f k b := by
  funext j; by_cases hj : j = k <;> simp [hj]

/-! ## Trie min/max (the `glass_min`/`glass_max` contract) -/

def lmin (l : List Nat) : Nat := l.foldl min U32_MAX
def lmax (l : List Nat) : Nat := l.foldl max 0

theorem foldl_min_le_init (l : List Nat) (a : Nat) : l.foldl min a ≤ a := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons]; have := ih (min a x); omega

theorem foldl_min_le_mem (l : List Nat) (a x : Nat) (hx : x ∈ l) : l.foldl min a ≤ x := by
  induction l generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | h
    · have := foldl_min_le_init ys (min a x); omega
    · exact ih _ h

theorem foldl_min_cases (l : List Nat) (a : Nat) : l.foldl min a = a ∨ l.foldl min a ∈ l := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rcases ih (min a x) with h | h
    · rw [h]; omega
    · exact Or.inr (Or.inr h)

theorem foldl_max_ge_init (l : List Nat) (a : Nat) : a ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons]; have := ih (max a x); omega

theorem foldl_max_ge_mem (l : List Nat) (a x : Nat) (hx : x ∈ l) : x ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | h
    · have := foldl_max_ge_init ys (max a x); omega
    · exact ih _ h

theorem foldl_max_cases (l : List Nat) (a : Nat) : l.foldl max a = a ∨ l.foldl max a ∈ l := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rcases ih (max a x) with h | h
    · rw [h]; omega
    · exact Or.inr (Or.inr h)

/-- `m` is the minimum of `l`, or `u32::MAX` (the paper's ∞) when `l` is empty. -/
def IsMinB (m : Nat) (l : List Nat) : Prop := (∀ x ∈ l, m ≤ x) ∧ (m ∈ l ∨ (l = [] ∧ m = U32_MAX))
/-- `m` is the maximum of `l`, or `0` when `l` is empty. -/
def IsMaxB (m : Nat) (l : List Nat) : Prop := (∀ x ∈ l, x ≤ m) ∧ (m ∈ l ∨ (l = [] ∧ m = 0))

theorem lmin_isMin (l : List Nat) (hr : ∀ x ∈ l, x ≤ U32_MAX) : IsMinB (lmin l) l := by
  refine ⟨fun x hx => foldl_min_le_mem l _ x hx, ?_⟩
  rcases foldl_min_cases l U32_MAX with h | h
  · cases l with
    | nil => exact Or.inr ⟨rfl, h⟩
    | cons y ys =>
      left
      have h1 := foldl_min_le_mem (y :: ys) U32_MAX y (by simp)
      have h2 := hr y (by simp)
      have : lmin (y :: ys) = y := by unfold lmin at *; omega
      rw [this]; simp
  · exact Or.inl h

theorem lmax_isMax (l : List Nat) : IsMaxB (lmax l) l := by
  refine ⟨fun x hx => foldl_max_ge_mem l _ x hx, ?_⟩
  rcases foldl_max_cases l 0 with h | h
  · cases l with
    | nil => exact Or.inr ⟨rfl, h⟩
    | cons y ys =>
      left
      have h1 := foldl_max_ge_mem (y :: ys) 0 y (by simp)
      have : lmax (y :: ys) = y := by unfold lmax at *; omega
      rw [this]; simp
  · exact Or.inl h

/-! ## The ordered key index (`preempt_keys: BTreeSet<u32>`) -/

/-- `BTreeSet::insert` on the ascending element list. -/
def sinsert (k : Nat) : List Nat → List Nat
  | [] => [k]
  | x :: xs => if k < x then k :: x :: xs else if k = x then x :: xs else x :: sinsert k xs

theorem mem_sinsert (k j : Nat) (l : List Nat) : j ∈ sinsert k l ↔ j = k ∨ j ∈ l := by
  induction l with
  | nil => simp [sinsert]
  | cons x xs ih =>
    unfold sinsert
    by_cases h1 : k < x
    · simp [h1]
    · by_cases h2 : k = x
      · subst h2; simp only [h1, if_false, if_true, List.mem_cons]
        constructor
        · intro h; exact Or.inr h
        · rintro (h | h | h) <;> first | exact Or.inl h | exact Or.inr h
      · simp only [h1, h2, if_false, List.mem_cons, ih]
        constructor
        · rintro (h | h | h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · rintro (h | h | h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)

theorem sorted_sinsert (k : Nat) (l : List Nat) (h : l.Pairwise (· < ·)) :
    (sinsert k l).Pairwise (· < ·) := by
  induction l with
  | nil => simp [sinsert]
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := List.pairwise_cons.mp h
    unfold sinsert
    by_cases h1 : k < x
    · simp only [h1, if_true]
      refine List.pairwise_cons.mpr ⟨fun a ha => ?_, h⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · exact h1
      · exact Nat.lt_trans h1 (hx a ha)
    · by_cases h2 : k = x
      · rw [if_neg h1, if_pos h2]; exact h
      · simp only [h1, h2, if_false]
        refine List.pairwise_cons.mpr ⟨fun a ha => ?_, ih hxs⟩
        rcases (mem_sinsert k a xs).mp ha with rfl | ha
        · omega
        · exact hx a ha

/-- The threshold an index implies: its first key, or `u32::MAX`. -/
def headD (l : List Nat) : Nat := l.head?.getD U32_MAX

theorem headD_sinsert (k : Nat) (l : List Nat) (hk : k ≤ U32_MAX) :
    headD (sinsert k l) = min (headD l) k := by
  cases l with
  | nil => simp [sinsert, headD]; omega
  | cons x xs =>
    unfold sinsert
    by_cases h1 : k < x
    · simp [h1, headD]; omega
    · by_cases h2 : k = x
      · subst h2; simp [headD]
      · simp [h1, h2, headD]; omega

theorem headD_erase_ne {l : List Nat} {k : Nat} (hk : k ≠ headD l) (hne : l ≠ []) :
    headD (l.erase k) = headD l := by
  cases l with
  | nil => exact absurd rfl hne
  | cons x xs =>
    have : k ≠ x := by simpa [headD] using hk
    have hb : ¬ ((x == k) = true) := by rw [beq_iff_eq]; exact fun e => this e.symm
    rw [List.erase_cons_tail hb]; simp [headD]

theorem sorted_nodup {l : List Nat} (h : l.Pairwise (· < ·)) : l.Nodup :=
  h.imp (fun h => Nat.ne_of_lt h)

theorem pairwise_lt_getLast {l : List Nat} (hs : l.Pairwise (· < ·)) (hne : l ≠ [])
    {y : Nat} (hy : y ∈ l) : y ≤ l.getLast hne := by
  induction l generalizing y with
  | nil => simp at hy
  | cons a as ih =>
    obtain ⟨ha, has⟩ := List.pairwise_cons.mp hs
    cases as with
    | nil => simp at hy; simp [hy]
    | cons b bs =>
      rw [List.getLast_cons (by simp)]
      rcases List.mem_cons.mp hy with rfl | hy
      · have hb : b ≤ (b :: bs).getLast (by simp) := ih has (by simp) (by simp)
        have := ha b (by simp); omega
      · exact ih has (by simp) hy

/-! ## State -/

structure St where
  /-- The trie tier, abstracted as a map (value `none` = no level). -/
  G : Map
  /-- Ghost: key set of `G`; `glass_size()` is its length. -/
  gk : List Nat
  /-- `preempt: AHashMap<u32, u64>`. -/
  P : Map
  /-- `preempt_keys: BTreeSet<u32>`, as its ascending element list. -/
  idx : List Nat
  /-- `thres: u32`. -/
  thres : Nat

/-- `Glass::new()` / `clear()` (src/lib.rs:263-293, 311-329), tier fields only. -/
def init : St := { G := fun _ => none, gk := [], P := fun _ => none, idx := [], thres := U32_MAX }

/-! ## Trie contract (abstract) -/

/-- `glass_insert` / a write through `glass_get_mut` (src/lib.rs:1456, 1663). -/
def glassInsert (s : St) (k v : Nat) : St :=
  { s with G := upd s.G k (some v), gk := if s.G k = none then k :: s.gk else s.gk }

/-- `glass_remove` (src/lib.rs:1675). -/
def glassRemove (s : St) (k : Nat) : St × Option Nat :=
  match s.G k with
  | none => (s, none)
  | some v => ({ s with G := upd s.G k none, gk := s.gk.erase k }, some v)

/-- `glass_min` (src/lib.rs:1811): the lowest trie key. -/
def glassMin (s : St) : Option (Nat × Nat) :=
  if s.gk = [] then none else (s.G (lmin s.gk)).map (lmin s.gk, ·)

/-- `glass_max` (src/lib.rs:1822): the highest trie key. -/
def glassMax (s : St) : Option (Nat × Nat) :=
  if s.gk = [] then none else (s.G (lmax s.gk)).map (lmax s.gk, ·)

/-! ## Preempt tier -/

/-- `refresh_thres` (src/lib.rs:771-774). -/
def refreshThres (s : St) : St := { s with thres := headD s.idx }

/-- `preempt_insert` (src/lib.rs:741-755). The `reserve` call only sizes the
table's capacity and has no semantic effect. -/
def preemptInsert (s : St) (k v : Nat) : St :=
  match s.P k with
  | some _ => { s with P := upd s.P k (some v) }
  | none => { s with P := upd s.P k (some v), idx := sinsert k s.idx, thres := min s.thres k }

/-- `preempt_remove` (src/lib.rs:758-768). -/
def preemptRemove (s : St) (k : Nat) : St × Option Nat :=
  match s.P k with
  | none => (s, none)
  | some v =>
    let s' := { s with P := upd s.P k none, idx := s.idx.erase k }
    (if k = s.thres then refreshThres s' else s', some v)

/-- `REFILL_BATCH` (src/lib.rs:62). -/
def REFILL_BATCH : Nat := 32

/-- The loop of `restructure` (src/lib.rs:955-972): pop the lowest index key
(never the pinned `u32::MAX`), take its level out of the map, insert it into
the trie. The map miss is `invariant_violated` in the Rust; the model stops
there instead, and `restructure_never_panics` shows it is unreachable. -/
def restructureLoop : Nat → St → St
  | 0, s => s
  | room + 1, s =>
    match s.idx with
    | [] => s
    | k :: rest =>
      if k = U32_MAX then s else
      match s.P k with
      | none => s
      | some v => restructureLoop room (glassInsert { s with idx := rest, P := upd s.P k none } k v)

/-- Whether the `restructure` loop would reach its `invariant_violated`. -/
def restructurePanics : Nat → St → Bool
  | 0, _ => false
  | room + 1, s =>
    match s.idx with
    | [] => false
    | k :: rest =>
      if k = U32_MAX then false else
      match s.P k with
      | none => true
      | some v => restructurePanics room (glassInsert { s with idx := rest, P := upd s.P k none } k v)

/-- `restructure` (src/lib.rs:955-975): refill up to `MAX_SIZE`
(`saturating_sub`), then `refresh_thres`. -/
def restructure (s : St) : St := refreshThres (restructureLoop (MAX_SIZE - s.gk.length) s)

/-- `refill_if_low` (src/lib.rs:943-948). -/
def refillIfLow (s : St) : St :=
  if s.gk.length ≤ MAX_SIZE - REFILL_BATCH ∧ s.idx ≠ [] then restructure s else s

/-! ## Public operations -/

/-- `get` (src/lib.rs:819-826), routed by `routes_to_trie` (src/lib.rs:912-915). -/
def get (s : St) (k : Nat) : Option Nat := if k < s.thres then s.G k else s.P k

/-- `remove` (src/lib.rs:896-908). -/
def remove (s : St) (k : Nat) : St × Option Nat :=
  if k < s.thres then
    let g := glassRemove s k
    if g.2.isSome then (refillIfLow g.1, g.2) else g
  else preemptRemove s k

/-- `insert_new_glass_key` (src/lib.rs:800-815): evict the trie max when full. -/
def insertNewGlassKey (s : St) (k v : Nat) : St :=
  if s.gk.length < MAX_SIZE then glassInsert s k v
  else match glassMax s with
    | some (wk, wv) =>
      if k < wk then glassInsert (preemptInsert (glassRemove s wk).1 wk wv) k v
      else preemptInsert s k v
    | none => glassInsert s k v

/-- `insert` (src/lib.rs:778-797). Value 0 deletes. -/
def insert (s : St) (k v : Nat) : St :=
  if v = 0 then (remove s k).1 else
  if k < s.thres then
    match s.G k with
    | some _ => glassInsert s k v
    | none => insertNewGlassKey s k v
  else preemptInsert s k v

/-- `update_value` (src/lib.rs:856-887) and `remove_zeroed_glass_value`
(src/lib.rs:889-893). In the trie branch a zeroed slot is set back to 1 before
`glass_remove`; in the preempt branch the map briefly stores 0 and
`preempt_remove` then drops it. -/
def updateValue (s : St) (k : Nat) (f : Nat → Nat) : St × Bool :=
  if k < s.thres then
    match s.G k with
    | none => (s, false)
    | some v =>
      if f v ≠ 0 then (glassInsert s k (f v), true)
      else (refillIfLow (glassRemove (glassInsert s k 1) k).1, true)
  else
    match s.P k with
    | none => (s, false)
    | some v =>
      let s' := { s with P := upd s.P k (some (f v)) }
      if f v = 0 then ((preemptRemove s' k).1, true) else (s', true)

/-- `min` (src/lib.rs:922-929). `preempt_qty`'s panic is modeled as
`Option.map`; `minOp_lookup_present` shows the key is always present. -/
def minOp (s : St) : Option (Nat × Nat) :=
  match glassMin s with
  | some t => some t
  | none =>
    match s.idx.head? with
    | none => none
    | some k => (s.P k).map (k, ·)

/-- `max` (src/lib.rs:932-938). -/
def maxOp (s : St) : Option (Nat × Nat) :=
  match s.idx.getLast? with
  | some k => (s.P k).map (k, ·)
  | none => glassMax s

/-! ## Invariant and abstraction -/

/-- Everything except the exactness of `thres` (which `restructure`'s loop
suspends until its final `refresh_thres`). -/
structure Inv0 (s : St) : Prop where
  gk_nodup : s.gk.Nodup
  gk_iff : ∀ k, s.G k ≠ none ↔ k ∈ s.gk
  /-- Trie capacity. -/
  gsize : s.gk.length ≤ MAX_SIZE
  /-- Value 0 means absent: no stored zeros. -/
  G_pos : ∀ k v, s.G k = some v → 0 < v
  /-- The index is strictly ascending (a set, in order). -/
  idx_sorted : s.idx.Pairwise (· < ·)
  /-- The index and the hash map hold the same key set. -/
  idx_iff : ∀ k, s.P k ≠ none ↔ k ∈ s.idx
  P_pos : ∀ k v, s.P k = some v → 0 < v
  /-- Keys are `u32`. -/
  idx_range : ∀ k ∈ s.idx, k ≤ U32_MAX
  /-- The tier invariant: every trie key is below every preempt key and below
  `u32::MAX` (so the trie never holds the pinned key). -/
  tier : ∀ g ∈ s.gk, g < U32_MAX ∧ ∀ p ∈ s.idx, g < p

/-- The full invariant: `thres` is exact. -/
def Inv (s : St) : Prop := Inv0 s ∧ s.thres = headD s.idx

/-- The book the two tiers jointly represent. -/
def abs (s : St) : Map := fun k => match s.G k with
  | some v => some v
  | none => s.P k

/-- Spec semantics of `insert`: plain map update, value 0 deletes. -/
def specInsert (b : Map) (k v : Nat) : Map := upd b k (if v = 0 then none else some v)

/-- Spec semantics of `update_value` (the paper's `adjust`). -/
def specUpdate (b : Map) (k : Nat) (f : Nat → Nat) : Map × Bool :=
  match b k with
  | none => (b, false)
  | some v => (upd b k (if f v = 0 then none else some (f v)), true)

/-- `r` is the lowest level of book `b` (or `none` iff `b` is empty). -/
def SpecMin (b : Map) : Option (Nat × Nat) → Prop
  | none => ∀ k, b k = none
  | some (k, v) => b k = some v ∧ ∀ j, b j ≠ none → k ≤ j

/-- `r` is the highest level of book `b` (or `none` iff `b` is empty). -/
def SpecMax (b : Map) : Option (Nat × Nat) → Prop
  | none => ∀ k, b k = none
  | some (k, v) => b k = some v ∧ ∀ j, b j ≠ none → j ≤ k

/-! ## Basic facts -/

theorem inv_init : Inv init :=
  ⟨⟨by simp [init], by simp [init], by simp [init, MAX_SIZE], by simp [init], by simp [init],
    by simp [init], by simp [init], by simp [init], by simp [init]⟩, by simp [init, headD]⟩

namespace Inv0
variable {s : St}

theorem G_none_iff (h : Inv0 s) (k : Nat) : s.G k = none ↔ k ∉ s.gk := by
  have := h.gk_iff k; constructor <;> intro h1
  · exact fun hm => (this.mpr hm) h1
  · exact Classical.byContradiction fun h2 => h1 (this.mp h2)

theorem P_none_iff (h : Inv0 s) (k : Nat) : s.P k = none ↔ k ∉ s.idx := by
  have := h.idx_iff k; constructor <;> intro h1
  · exact fun hm => (this.mpr hm) h1
  · exact Classical.byContradiction fun h2 => h1 (this.mp h2)

theorem idx_nodup (h : Inv0 s) : s.idx.Nodup := sorted_nodup h.idx_sorted

/-- The tiers are disjoint. -/
theorem not_mem_idx_of_mem_gk (h : Inv0 s) {k : Nat} (hk : k ∈ s.gk) : k ∉ s.idx := by
  intro hp; have := (h.tier k hk).2 k hp; omega

theorem P_none_of_G (h : Inv0 s) {k v : Nat} (hk : s.G k = some v) : s.P k = none :=
  (h.P_none_iff k).mpr (h.not_mem_idx_of_mem_gk ((h.gk_iff k).mp (by simp [hk])))

theorem G_some_of_mem (h : Inv0 s) {k : Nat} (hk : k ∈ s.gk) : ∃ v, s.G k = some v := by
  have := (h.gk_iff k).mpr hk; cases hh : s.G k <;> simp_all

theorem P_some_of_mem (h : Inv0 s) {k : Nat} (hk : k ∈ s.idx) : ∃ v, s.P k = some v := by
  have := (h.idx_iff k).mpr hk; cases hh : s.P k <;> simp_all

end Inv0

namespace Inv
variable {s : St}

/-- A key routed to the trie is below every preempt key and below `u32::MAX`. -/
theorem lt_thres (h : Inv s) {k : Nat} (hk : k < s.thres) :
    k < U32_MAX ∧ ∀ p ∈ s.idx, k < p := by
  obtain ⟨h0, ht⟩ := h
  rw [ht] at hk
  have hs := h0.idx_sorted
  have hr := h0.idx_range
  cases hi : s.idx with
  | nil => rw [hi] at hk; simp [headD] at hk; exact ⟨hk, by simp⟩
  | cons x xs =>
    rw [hi] at hk hs hr; simp [headD] at hk
    obtain ⟨hx, _⟩ := List.pairwise_cons.mp hs
    have hxr := hr x (by simp)
    refine ⟨by omega, fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hk
    · exact Nat.lt_trans hk (hx p hp)

/-- Every trie key is below the threshold. -/
theorem gk_lt_thres (h : Inv s) {g : Nat} (hg : g ∈ s.gk) : g < s.thres := by
  obtain ⟨h0, ht⟩ := h
  rw [ht]; obtain ⟨hmax, hlt⟩ := h0.tier g hg
  cases hi : s.idx with
  | nil => simpa [headD] using hmax
  | cons x xs => simp [headD]; exact hlt x (by simp [hi])

/-- Routing to the trie never hits a preempt key. -/
theorem P_none_of_lt (h : Inv s) {k : Nat} (hk : k < s.thres) : s.P k = none :=
  (h.1.P_none_iff k).mpr (fun hm => by have := (h.lt_thres hk).2 k hm; omega)

/-- Routing to the preempt tier never hits a trie key. -/
theorem G_none_of_ge (h : Inv s) {k : Nat} (hk : ¬ k < s.thres) : s.G k = none :=
  (h.1.G_none_iff k).mpr (fun hm => hk (h.gk_lt_thres hm))

end Inv

/-- Pointwise description of `abs`. -/
theorem abs_apply (t : St) (j : Nat) : abs t j = (t.G j).or (t.P j) := by
  simp only [abs]; cases t.G j <;> rfl

theorem abs_congr {s t : St} (hG : s.G = t.G) (hP : s.P = t.P) : abs s = abs t := by
  funext k; simp [abs, hG, hP]

/-- `get` returns exactly the book's level. -/
theorem get_correct {s : St} (h : Inv s) (k : Nat) : get s k = abs s k := by
  unfold get; split
  · rename_i hk; simp [abs_apply, h.P_none_of_lt hk]
  · rename_i hk; simp [abs_apply, h.G_none_of_ge hk]

/-! ## Primitive lemmas -/

section Prims
variable {s : St}

@[simp] theorem glassInsert_P (k v : Nat) : (glassInsert s k v).P = s.P := rfl
@[simp] theorem glassInsert_idx (k v : Nat) : (glassInsert s k v).idx = s.idx := rfl
@[simp] theorem glassInsert_thres (k v : Nat) : (glassInsert s k v).thres = s.thres := rfl
@[simp] theorem glassInsert_G (k v : Nat) : (glassInsert s k v).G = upd s.G k (some v) := rfl

theorem glassInsert_gk_mem (h : Inv0 s) (k v j : Nat) :
    j ∈ (glassInsert s k v).gk ↔ j = k ∨ j ∈ s.gk := by
  simp only [glassInsert]; split
  · simp
  · rename_i hne; have := (h.gk_iff k).mp hne; constructor
    · exact Or.inr
    · rintro (rfl | h1) <;> assumption

theorem glassInsert_inv0 (h : Inv0 s) {k v : Nat} (hv : 0 < v)
    (hsz : s.G k = none → s.gk.length < MAX_SIZE)
    (hk : k < U32_MAX) (hkp : ∀ p ∈ s.idx, k < p) : Inv0 (glassInsert s k v) := by
  have mem_iff := glassInsert_gk_mem h k v
  refine ⟨?_, ?_, ?_, ?_, h.idx_sorted, h.idx_iff, h.P_pos, h.idx_range, ?_⟩
  · simp only [glassInsert]; split
    · rename_i hn; exact List.nodup_cons.mpr ⟨(h.G_none_iff k).mp hn, h.gk_nodup⟩
    · exact h.gk_nodup
  · intro j; rw [mem_iff]; by_cases hj : j = k
    · subst hj; simp
    · simp [hj, h.gk_iff j]
  · simp only [glassInsert]; split
    · rename_i hn; have := hsz hn; simp; omega
    · exact h.gsize
  · intro j w hw; simp only [glassInsert_G, upd_apply] at hw; split at hw
    · cases hw; exact hv
    · exact h.G_pos j w hw
  · intro g hg; rcases (mem_iff g).mp hg with rfl | hg
    · exact ⟨hk, hkp⟩
    · exact h.tier g hg

theorem glassInsert_inv (h : Inv s) {k v : Nat} (hv : 0 < v)
    (hsz : s.G k = none → s.gk.length < MAX_SIZE)
    (hk : k < U32_MAX) (hkp : ∀ p ∈ s.idx, k < p) : Inv (glassInsert s k v) :=
  ⟨glassInsert_inv0 h.1 hv hsz hk hkp, by simpa using h.2⟩

@[simp] theorem glassRemove_snd (k : Nat) : (glassRemove s k).2 = s.G k := by
  unfold glassRemove; split <;> simp_all
@[simp] theorem glassRemove_P (k : Nat) : (glassRemove s k).1.P = s.P := by
  unfold glassRemove; split <;> rfl
@[simp] theorem glassRemove_idx (k : Nat) : (glassRemove s k).1.idx = s.idx := by
  unfold glassRemove; split <;> rfl
@[simp] theorem glassRemove_thres (k : Nat) : (glassRemove s k).1.thres = s.thres := by
  unfold glassRemove; split <;> rfl
@[simp] theorem glassRemove_G (k : Nat) : (glassRemove s k).1.G = upd s.G k none := by
  unfold glassRemove; split
  · rename_i hn; funext j; by_cases hj : j = k <;> simp_all
  · rfl

theorem glassRemove_gk_mem (h : Inv0 s) (k j : Nat) :
    j ∈ (glassRemove s k).1.gk ↔ j ≠ k ∧ j ∈ s.gk := by
  unfold glassRemove; split
  · rename_i hn; have := (h.G_none_iff k).mp hn
    constructor
    · intro hj; exact ⟨fun e => this (e ▸ hj), hj⟩
    · exact fun h1 => h1.2
  · exact h.gk_nodup.mem_erase_iff

theorem glassRemove_inv0 (h : Inv0 s) (k : Nat) : Inv0 (glassRemove s k).1 := by
  have hm := glassRemove_gk_mem h k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold glassRemove; split
    · exact h.gk_nodup
    · exact h.gk_nodup.erase k
  · intro j; rw [hm]; by_cases hj : j = k <;> simp [hj, h.gk_iff j]
  · have : (glassRemove s k).1.gk.length ≤ s.gk.length := by
      unfold glassRemove; split
      · exact Nat.le_refl _
      · exact (List.erase_sublist).length_le
    exact Nat.le_trans this h.gsize
  · intro j w hw; simp only [glassRemove_G, upd_apply] at hw; split at hw
    · cases hw
    · exact h.G_pos j w hw
  · simpa using h.idx_sorted
  · simpa using h.idx_iff
  · simpa using h.P_pos
  · simpa using h.idx_range
  · intro g hg; simpa using h.tier g ((hm g).mp hg).2

theorem glassRemove_inv (h : Inv s) (k : Nat) : Inv (glassRemove s k).1 :=
  ⟨glassRemove_inv0 h.1 k, by simpa using h.2⟩

@[simp] theorem preemptInsert_G (k v : Nat) : (preemptInsert s k v).G = s.G := by
  unfold preemptInsert; split <;> rfl
@[simp] theorem preemptInsert_gk (k v : Nat) : (preemptInsert s k v).gk = s.gk := by
  unfold preemptInsert; split <;> rfl
@[simp] theorem preemptInsert_P (k v : Nat) : (preemptInsert s k v).P = upd s.P k (some v) := by
  unfold preemptInsert; split <;> rfl

theorem preemptInsert_idx_mem (h : Inv0 s) (k v j : Nat) :
    j ∈ (preemptInsert s k v).idx ↔ j = k ∨ j ∈ s.idx := by
  unfold preemptInsert; split
  · rename_i w hw
    have hk : k ∈ s.idx := (h.idx_iff k).mp (by simp [hw])
    simp only; constructor
    · exact Or.inr
    · rintro (rfl | h1) <;> assumption
  · exact mem_sinsert k j s.idx

/-- `preempt_insert` keeps the invariant, including an exact `thres`. -/
theorem preemptInsert_inv (h : Inv s) {k v : Nat} (hv : 0 < v) (hk : k ≤ U32_MAX)
    (hg : ∀ g ∈ s.gk, g < k) : Inv (preemptInsert s k v) := by
  have mem_iff := preemptInsert_idx_mem h.1 k v
  have h0 := h.1
  refine ⟨⟨by simpa using h0.gk_nodup, by simpa using h0.gk_iff, by simpa using h0.gsize,
    by simpa using h0.G_pos, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · unfold preemptInsert; split
    · exact h0.idx_sorted
    · exact sorted_sinsert k _ h0.idx_sorted
  · intro j; rw [mem_iff]; by_cases hj : j = k
    · subst hj; simp
    · simp [hj, h0.idx_iff j]
  · intro j w hw; simp only [preemptInsert_P, upd_apply] at hw; split at hw
    · cases hw; exact hv
    · exact h0.P_pos j w hw
  · intro j hj; rcases (mem_iff j).mp hj with rfl | hj
    · exact hk
    · exact h0.idx_range j hj
  · intro g hgm; simp only [preemptInsert_gk] at hgm
    refine ⟨(h0.tier g hgm).1, fun p hp => ?_⟩
    rcases (mem_iff p).mp hp with rfl | hp
    · exact hg g hgm
    · exact (h0.tier g hgm).2 p hp
  · unfold preemptInsert; split
    · exact h.2
    · simp only; rw [headD_sinsert k _ hk, ← h.2]

@[simp] theorem preemptRemove_snd (k : Nat) : (preemptRemove s k).2 = s.P k := by
  unfold preemptRemove; split
  · simp_all
  · simp_all

@[simp] theorem preemptRemove_G (k : Nat) : (preemptRemove s k).1.G = s.G := by
  unfold preemptRemove; split
  · rfl
  · simp only; split <;> rfl
@[simp] theorem preemptRemove_gk (k : Nat) : (preemptRemove s k).1.gk = s.gk := by
  unfold preemptRemove; split
  · rfl
  · simp only; split <;> rfl
@[simp] theorem preemptRemove_P (k : Nat) : (preemptRemove s k).1.P = upd s.P k none := by
  unfold preemptRemove; split
  · rename_i hn; funext j; by_cases hj : j = k <;> simp_all
  · simp only; split <;> rfl

/-- `preempt_remove` keeps the invariant, including an exact `thres`. -/
theorem preemptRemove_inv (h : Inv s) (k : Nat) : Inv (preemptRemove s k).1 := by
  unfold preemptRemove
  split
  · exact h
  rename_i v hv
  have h0 := h.1
  have hk : k ∈ s.idx := (h0.idx_iff k).mp (by simp [hv])
  have mem_iff : ∀ j, j ∈ s.idx.erase k ↔ j ≠ k ∧ j ∈ s.idx := fun j => h0.idx_nodup.mem_erase_iff
  have base : ∀ th, Inv0 { s with P := upd s.P k none, idx := s.idx.erase k, thres := th } := by
    intro th
    refine ⟨h0.gk_nodup, h0.gk_iff, h0.gsize, h0.G_pos,
      h0.idx_sorted.sublist List.erase_sublist, ?_, ?_, ?_, ?_⟩
    · intro j; simp only; rw [mem_iff]; by_cases hj : j = k
      · subst hj; simp
      · simp [hj, h0.idx_iff j]
    · intro j w hw; simp only [upd_apply] at hw; split at hw
      · cases hw
      · exact h0.P_pos j w hw
    · intro j hj; exact h0.idx_range j ((mem_iff j).mp hj).2
    · intro g hg
      exact ⟨(h0.tier g hg).1, fun p hp => (h0.tier g hg).2 p ((mem_iff p).mp hp).2⟩
  simp only
  split
  · exact ⟨base _, rfl⟩
  · rename_i hne
    refine ⟨base _, ?_⟩
    simp only
    have hl : s.idx ≠ [] := fun he => by simp [he] at hk
    rw [headD_erase_ne (by rw [← h.2]; exact hne) hl, h.2]

theorem preemptRemove_after_write (s : St) (k w : Nat) (hk : s.P k ≠ none) :
    (preemptRemove { s with P := upd s.P k (some w) } k).1 = (preemptRemove s k).1 := by
  obtain ⟨v, hv⟩ : ∃ v, s.P k = some v := by cases hh : s.P k <;> simp_all
  unfold preemptRemove
  simp only [upd_self, hv]
  split <;> simp [upd_upd, refreshThres]

end Prims

/-! ## restructure -/

section Restructure

/-- One step of the refill loop keeps `Inv0` and the book; and the loop never
reaches its `invariant_violated`. -/
theorem restructureLoop_correct : ∀ (room : Nat) (s : St), Inv0 s →
    s.gk.length + room ≤ MAX_SIZE →
    Inv0 (restructureLoop room s) ∧ abs (restructureLoop room s) = abs s ∧
    restructurePanics room s = false
  | 0, s, h, _ => ⟨h, rfl, rfl⟩
  | room + 1, s, h, hr => by
    cases hi : s.idx with
    | nil =>
      simp only [restructureLoop, restructurePanics, hi]
      exact ⟨h, trivial, trivial⟩
    | cons k rest =>
      by_cases hkm : k = U32_MAX
      · simp only [restructureLoop, restructurePanics, hi, hkm, if_true]
        exact ⟨h, trivial, trivial⟩
      have hkidx : k ∈ s.idx := by simp [hi]
      obtain ⟨v, hv⟩ := h.P_some_of_mem hkidx
      simp only [restructureLoop, restructurePanics, hi, hkm, if_false, hv]
      have hs := h.idx_sorted; rw [hi] at hs
      obtain ⟨hkrest, hrest⟩ := List.pairwise_cons.mp hs
      have hkg : k ∉ s.gk := fun hg => h.not_mem_idx_of_mem_gk hg hkidx
      have hGk : s.G k = none := (h.G_none_iff k).mpr hkg
      -- the state with k popped from the index and taken out of the map
      have ht : Inv0 { s with idx := rest, P := upd s.P k none } := by
        refine ⟨h.gk_nodup, h.gk_iff, h.gsize, h.G_pos, hrest, ?_, ?_, ?_, ?_⟩
        · intro j; simp only; by_cases hj : j = k
          · subst hj; simp only [upd_self, ne_eq, not_true_eq_false, false_iff]
            intro hm; have := hkrest j hm; omega
          · rw [upd_ne _ _ hj, h.idx_iff j, hi]; simp [hj]
        · intro j w hw; simp only [upd_apply] at hw; split at hw
          · cases hw
          · exact h.P_pos j w hw
        · intro j hj; exact h.idx_range j (by simp [hi, hj])
        · intro g hg; exact ⟨(h.tier g hg).1, fun p hp => (h.tier g hg).2 p (by simp [hi, hp])⟩
      have hkmax : k < U32_MAX := by
        have := h.idx_range k hkidx; omega
      have hu := glassInsert_inv0 (s := { s with idx := rest, P := upd s.P k none }) ht
        (k := k) (v := v) (h.P_pos k v hv) (fun _ => by show s.gk.length < MAX_SIZE; omega)
        hkmax hkrest
      have hlen : (glassInsert { s with idx := rest, P := upd s.P k none } k v).gk.length =
          s.gk.length + 1 := by simp [glassInsert, hGk]
      obtain ⟨i1, i2, i3⟩ := restructureLoop_correct room _ hu (by rw [hlen]; omega)
      refine ⟨i1, ?_, i3⟩
      rw [i2]; funext j; simp only [abs_apply, glassInsert_G, glassInsert_P]
      by_cases hj : j = k
      · subst hj; simp [hGk, hv]
      · simp [hj]

/-- `restructure`'s `invariant_violated` (a popped index key missing from the
map) is unreachable. -/
theorem restructure_never_panics {s : St} (h : Inv s) :
    restructurePanics (MAX_SIZE - s.gk.length) s = false :=
  (restructureLoop_correct (MAX_SIZE - s.gk.length) s h.1 (by have := h.1.gsize; omega)).2.2

/-- `refresh_thres` only rewrites `thres`, which `Inv0` does not mention;
it makes `thres` exact. -/
theorem refreshThres_inv {s : St} (h : Inv0 s) : Inv (refreshThres s) :=
  ⟨⟨h.gk_nodup, h.gk_iff, h.gsize, h.G_pos, h.idx_sorted, h.idx_iff, h.P_pos, h.idx_range, h.tier⟩,
    rfl⟩

/-- `restructure` preserves the invariant and the book. -/
theorem restructure_correct {s : St} (h : Inv s) :
    Inv (restructure s) ∧ abs (restructure s) = abs s := by
  obtain ⟨i1, i2, _⟩ := restructureLoop_correct (MAX_SIZE - s.gk.length) s h.1 (by have := h.1.gsize; omega)
  exact ⟨refreshThres_inv i1, i2⟩

theorem refillIfLow_correct {s : St} (h : Inv s) :
    Inv (refillIfLow s) ∧ abs (refillIfLow s) = abs s := by
  unfold refillIfLow; split
  · exact restructure_correct h
  · exact ⟨h, rfl⟩

end Restructure

/-! ## remove, insert, update_value -/

section Ops
variable {s : St}

/-- `remove` deletes exactly `k` and returns its old level. -/
theorem remove_correct (h : Inv s) (k : Nat) :
    Inv (remove s k).1 ∧ abs (remove s k).1 = upd (abs s) k none ∧ (remove s k).2 = abs s k := by
  unfold remove
  split
  · rename_i hb
    have hP := h.P_none_of_lt hb
    have hg := glassRemove_inv h k
    have habs : abs (glassRemove s k).1 = upd (abs s) k none := by
      funext j; simp only [abs_apply, glassRemove_G, glassRemove_P, upd_apply]
      split
      · rename_i hj; subst hj; simp [hP]
      · rfl
    have hres : (glassRemove s k).2 = abs s k := by
      simp [abs_apply, hP]
    dsimp only
    split
    · obtain ⟨h1, h2⟩ := refillIfLow_correct hg
      exact ⟨h1, h2.trans habs, hres⟩
    · exact ⟨hg, habs, hres⟩
  · rename_i hb
    have hG := h.G_none_of_ge hb
    refine ⟨preemptRemove_inv h k, ?_, by simp [abs_apply, hG]⟩
    funext j; simp only [abs_apply, preemptRemove_G, preemptRemove_P, upd_apply]
    split
    · rename_i hj; subst hj; simp [hG]
    · rfl

theorem lmax_mem (hne : s.gk ≠ []) : lmax s.gk ∈ s.gk := by
  rcases (lmax_isMax s.gk).2 with hm | ⟨he, _⟩
  · exact hm
  · exact absurd he hne

theorem lmin_mem (h : Inv0 s) (hne : s.gk ≠ []) : lmin s.gk ∈ s.gk := by
  rcases (lmin_isMin s.gk (fun x hx => Nat.le_of_lt (h.tier x hx).1)).2 with hm | ⟨he, _⟩
  · exact hm
  · exact absurd he hne

/-- `insert` is a plain map update (value 0 deletes), including the eviction
of the trie maximum into the preempt tier when the trie is full. -/
theorem insert_correct (h : Inv s) {k v : Nat} (hk : k ≤ U32_MAX) :
    Inv (insert s k v) ∧ abs (insert s k v) = specInsert (abs s) k v := by
  unfold insert
  split
  · rename_i hv; obtain ⟨h1, h2, _⟩ := remove_correct h k
    exact ⟨h1, by simp [h2, specInsert, hv]⟩
  rename_i hv0
  have hvpos : 0 < v := Nat.pos_of_ne_zero hv0
  have hspec : specInsert (abs s) k v = upd (abs s) k (some v) := by simp [specInsert, hv0]
  rw [hspec]
  have abs_gi : ∀ t : St, (∀ j, j ≠ k → abs t j = abs s j) → t.G k = some v →
      abs t = upd (abs s) k (some v) := by
    intro t ht hk'; funext j; by_cases hj : j = k
    · subst hj; simp [abs_apply, hk']
    · simp [hj, ht j hj]
  split
  · rename_i hb
    have hlt := h.lt_thres hb
    split
    · rename_i w hw
      refine ⟨glassInsert_inv h hvpos (fun hn => by simp [hw] at hn) hlt.1 hlt.2,
        abs_gi _ (fun j hj => by simp [abs_apply, hj]) (by simp)⟩
    · rename_i hGk
      unfold insertNewGlassKey
      split
      · rename_i hlen
        exact ⟨glassInsert_inv h hvpos (fun _ => hlen) hlt.1 hlt.2,
          abs_gi _ (fun j hj => by simp [abs_apply, hj]) (by simp)⟩
      · rename_i hlen
        have hne : s.gk ≠ [] := by intro he; simp [he, MAX_SIZE] at hlen
        have hwk := lmax_mem hne
        obtain ⟨wv, hwv⟩ := h.1.G_some_of_mem hwk
        have hgm : glassMax s = some (lmax s.gk, wv) := by simp [glassMax, hne, hwv]
        rw [hgm]; simp only
        have hkg : k ∉ s.gk := (h.1.G_none_iff k).mp hGk
        have hub : ∀ g ∈ s.gk, g ≤ lmax s.gk := (lmax_isMax s.gk).1
        split
        · rename_i hkw
          have h1 := glassRemove_inv h (lmax s.gk)
          have hwpos := h.1.G_pos _ _ hwv
          have hwlt := (h.1.tier _ hwk).1
          have h2 := preemptInsert_inv h1 (v := wv) hwpos (Nat.le_of_lt hwlt) (fun g hg => by
            rw [glassRemove_gk_mem h.1] at hg
            exact Nat.lt_of_le_of_ne (hub g hg.2) hg.1)
          have hsz : (glassRemove s (lmax s.gk)).1.gk.length < MAX_SIZE := by
            unfold glassRemove; rw [hwv]; simp only
            rw [List.length_erase_of_mem hwk]; have := h.1.gsize
            have : 0 < s.gk.length := List.length_pos_iff.mpr hne
            omega
          refine ⟨glassInsert_inv h2 hvpos (fun _ => by simpa using hsz) hlt.1 (fun p hp => ?_), ?_⟩
          · rw [preemptInsert_idx_mem h1.1] at hp
            rcases hp with rfl | hp
            · exact hkw
            · simp only [glassRemove_idx] at hp; exact hlt.2 p hp
          · refine abs_gi _ (fun j hj => ?_) (by simp)
            simp only [abs_apply, glassInsert_G, preemptInsert_G, preemptInsert_P, glassInsert_P,
              glassRemove_G, glassRemove_P, upd_apply, hj, if_false]
            split
            · rename_i hjw; subst hjw; simp [hwv]
            · rfl
        · rename_i hkw
          refine ⟨preemptInsert_inv h hvpos hk (fun g hg => ?_), ?_⟩
          · have := hub g hg
            exact Nat.lt_of_le_of_ne (by omega) (fun e => hkg (e ▸ hg))
          · funext j; by_cases hj : j = k
            · subst hj; simp [abs_apply, hGk]
            · simp [abs_apply, hj]
  · rename_i hb
    have hGk : s.G k = none := h.G_none_of_ge hb
    refine ⟨preemptInsert_inv h hvpos hk (fun g hg => ?_), ?_⟩
    · have := h.gk_lt_thres hg; omega
    · funext j; by_cases hj : j = k
      · subst hj; simp [abs_apply, hGk]
      · simp [abs_apply, hj]

/-- `update_value` is the paper's `adjust`: apply `f`, and a result of 0
removes the level (never leaves a stored zero behind). -/
theorem updateValue_correct (h : Inv s) (k : Nat) (f : Nat → Nat) :
    Inv (updateValue s k f).1 ∧ abs (updateValue s k f).1 = (specUpdate (abs s) k f).1 ∧
    (updateValue s k f).2 = (specUpdate (abs s) k f).2 := by
  unfold updateValue
  split
  · rename_i hb
    have hP := h.P_none_of_lt hb
    have hlt := h.lt_thres hb
    split
    · rename_i hGk
      have hab : abs s k = none := by simp [abs_apply, hP, hGk]
      simp [specUpdate, hab, h]
    · rename_i v hGk
      have hab : abs s k = some v := by simp [abs_apply, hGk]
      simp only [specUpdate, hab]
      split
      · rename_i hf
        refine ⟨glassInsert_inv h (Nat.pos_of_ne_zero hf) (fun hn => by simp [hGk] at hn)
          hlt.1 hlt.2, ?_, rfl⟩
        try rw [if_neg hf]
        funext j; by_cases hj : j = k
        · subst hj; simp [abs_apply]
        · simp [abs_apply, hj]
      · rename_i hf; simp only [Decidable.not_not] at hf
        have h1 := glassInsert_inv h (v := 1) (by decide) (fun hn => by simp [hGk] at hn)
          hlt.1 hlt.2
        have h2 := glassRemove_inv h1 k
        have habs : abs (glassRemove (glassInsert s k 1) k).1 = upd (abs s) k none := by
          funext j; by_cases hj : j = k
          · subst hj; simp [abs_apply, hP]
          · simp [abs_apply, hj]
        try rw [if_pos hf]
        obtain ⟨h3, h4⟩ := refillIfLow_correct h2; exact ⟨h3, h4.trans habs, rfl⟩
  · rename_i hb
    have hG := h.G_none_of_ge hb
    split
    · rename_i hPk
      have hab : abs s k = none := by simp [abs_apply, hG, hPk]
      simp [specUpdate, hab, h]
    · rename_i v hPk
      have hab : abs s k = some v := by simp [abs_apply, hG, hPk]
      simp only [specUpdate, hab]
      split
      · rename_i hf
        rw [preemptRemove_after_write _ k (f v) (by simp [hPk])]
        refine ⟨preemptRemove_inv h k, ?_, rfl⟩
        try rw [if_pos hf]
        funext j; by_cases hj : j = k
        · subst hj; simp [abs_apply, hG]
        · simp [abs_apply, hj]
      · rename_i hf
        refine ⟨⟨{ h.1 with
            idx_iff := fun j => by
              show upd s.P k (some (f v)) j ≠ none ↔ j ∈ s.idx
              by_cases hj : j = k
              · subst hj
                simp only [upd_self, ne_eq, reduceCtorEq, not_false_eq_true, true_iff]
                exact (h.1.idx_iff j).mp (by simp [hPk])
              · rw [upd_ne _ _ hj]; exact h.1.idx_iff j
            P_pos := fun j w hw => by
              simp only [upd_apply] at hw; split at hw
              · cases hw; exact Nat.pos_of_ne_zero hf
              · exact h.1.P_pos j w hw }, h.2⟩, ?_, rfl⟩
        try rw [if_neg hf]
        funext j; by_cases hj : j = k
        · subst hj; simp [abs_apply, hG]
        · simp [abs_apply, hj]

end Ops

/-! ## min / max -/

section MinMax
variable {s : St}

theorem SpecMin.unique {b : Map} {r r' : Option (Nat × Nat)} (h : SpecMin b r) (h' : SpecMin b r') :
    r = r' := by
  match r, r', h, h' with
  | none, none, _, _ => rfl
  | none, some (k, v), h, h' => simp [SpecMin] at h h'; simp [h] at h'
  | some (k, v), none, h, h' => simp [SpecMin] at h h'; simp [h'] at h
  | some (k, v), some (k', v'), h, h' =>
    simp only [SpecMin] at h h'
    have e1 := h.2 k' (by simp [h'.1]); have e2 := h'.2 k (by simp [h.1])
    have : k = k' := by omega
    subst this; rw [h.1] at h'; cases h'.1; rfl

theorem SpecMax.unique {b : Map} {r r' : Option (Nat × Nat)} (h : SpecMax b r) (h' : SpecMax b r') :
    r = r' := by
  match r, r', h, h' with
  | none, none, _, _ => rfl
  | none, some (k, v), h, h' => simp [SpecMax] at h h'; simp [h] at h'
  | some (k, v), none, h, h' => simp [SpecMax] at h h'; simp [h'] at h
  | some (k, v), some (k', v'), h, h' =>
    simp only [SpecMax] at h h'
    have e1 := h.2 k' (by simp [h'.1]); have e2 := h'.2 k (by simp [h.1])
    have : k = k' := by omega
    subst this; rw [h.1] at h'; cases h'.1; rfl

theorem mem_of_abs (h : Inv0 s) {j : Nat} (hj : abs s j ≠ none) : j ∈ s.gk ∨ j ∈ s.idx := by
  rw [abs_apply] at hj
  cases hG : s.G j with
  | some _ => exact Or.inl ((h.gk_iff j).mp (by simp [hG]))
  | none => rw [hG] at hj; exact Or.inr ((h.idx_iff j).mp (by simpa using hj))

theorem glassMin_none (h : Inv0 s) (hm : glassMin s = none) : s.gk = [] := by
  unfold glassMin at hm; split at hm
  · assumption
  · rename_i hne; obtain ⟨v, hv⟩ := h.G_some_of_mem (lmin_mem h hne); simp [hv] at hm

/-- `min`'s `preempt_qty` lookup always finds its key: its
`invariant_violated` is unreachable. -/
theorem minOp_lookup_present (h : Inv0 s) {k : Nat} (hk : s.idx.head? = some k) :
    s.P k ≠ none := by
  obtain ⟨t, ht⟩ := List.head?_eq_some_iff.mp hk
  exact (h.idx_iff k).mpr (by simp [ht])

/-- `max`'s `preempt_qty` lookup always finds its key. -/
theorem maxOp_lookup_present (h : Inv0 s) {k : Nat} (hk : s.idx.getLast? = some k) :
    s.P k ≠ none := by
  obtain ⟨t, ht⟩ := List.getLast?_eq_some_iff.mp hk
  exact (h.idx_iff k).mpr (by simp [ht])

/-- `min` returns the lowest level of the book (and `none` iff it is empty). -/
theorem minOp_correct (h : Inv s) : SpecMin (abs s) (minOp s) := by
  have h0 := h.1
  unfold minOp
  split
  · rename_i t hgm
    unfold glassMin at hgm; split at hgm
    · cases hgm
    rename_i hne
    have hmem := lmin_mem h0 hne
    obtain ⟨v, hv⟩ := h0.G_some_of_mem hmem
    simp only [hv, Option.map_some, Option.some.injEq] at hgm; subst hgm
    refine ⟨by simp [abs_apply, hv], fun j hj => ?_⟩
    rcases mem_of_abs h0 hj with hg | hp
    · exact (lmin_isMin s.gk (fun x hx => Nat.le_of_lt (h0.tier x hx).1)).1 j hg
    · exact Nat.le_of_lt ((h0.tier _ hmem).2 j hp)
  · rename_i hgm
    have hgk := glassMin_none h0 hgm
    split
    · rename_i hhd
      intro j
      have hG : s.G j = none := (h0.G_none_iff j).mpr (by simp [hgk])
      have hi : s.idx = [] := List.head?_eq_none_iff.mp hhd
      have hP : s.P j = none := (h0.P_none_iff j).mpr (by simp [hi])
      simp [abs_apply, hG, hP]
    · rename_i k hhd
      obtain ⟨v, hv⟩ : ∃ v, s.P k = some v := by
        have := minOp_lookup_present h0 hhd; cases hh : s.P k <;> simp_all
      obtain ⟨t, ht⟩ := List.head?_eq_some_iff.mp hhd
      simp only [hv, Option.map_some, SpecMin]
      have hGk : s.G k = none := (h0.G_none_iff k).mpr (by simp [hgk])
      refine ⟨by simp [abs_apply, hGk, hv], fun j hj => ?_⟩
      rcases mem_of_abs h0 hj with hg | hp
      · simp [hgk] at hg
      · have hs := h0.idx_sorted; rw [ht] at hs hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact Nat.le_refl _
        · exact Nat.le_of_lt ((List.pairwise_cons.mp hs).1 j hp)

/-- `max` returns the highest level of the book (and `none` iff it is empty). -/
theorem maxOp_correct (h : Inv s) : SpecMax (abs s) (maxOp s) := by
  have h0 := h.1
  unfold maxOp
  split
  · rename_i k hl
    obtain ⟨v, hv⟩ : ∃ v, s.P k = some v := by
      have := maxOp_lookup_present h0 hl; cases hh : s.P k <;> simp_all
    obtain ⟨t, ht⟩ := List.getLast?_eq_some_iff.mp hl
    have hmem : k ∈ s.idx := by simp [ht]
    simp only [hv, Option.map_some, SpecMax]
    have hGk : s.G k = none := (h0.G_none_iff k).mpr (fun hg => h0.not_mem_idx_of_mem_gk hg hmem)
    refine ⟨by simp [abs_apply, hGk, hv], fun j hj => ?_⟩
    rcases mem_of_abs h0 hj with hg | hp
    · exact Nat.le_of_lt ((h0.tier j hg).2 _ hmem)
    · have hs := h0.idx_sorted; rw [ht] at hs hp
      rcases List.mem_append.mp hp with hp | hp
      · exact Nat.le_of_lt ((List.pairwise_append.mp hs).2.2 j hp k (by simp))
      · simp at hp; omega
  · rename_i hl
    have hi : s.idx = [] := List.getLast?_eq_none_iff.mp hl
    unfold glassMax; split
    · rename_i hgk; intro j
      have hG : s.G j = none := (h0.G_none_iff j).mpr (by simp [hgk])
      have hP : s.P j = none := (h0.P_none_iff j).mpr (by simp [hi])
      simp [abs_apply, hG, hP]
    · rename_i hne
      have hmem := lmax_mem hne
      obtain ⟨v, hv⟩ := h0.G_some_of_mem hmem
      simp only [hv, Option.map_some, SpecMax]
      refine ⟨by simp [abs_apply, hv], fun j hj => ?_⟩
      rcases mem_of_abs h0 hj with hg | hp
      · exact (lmax_isMax s.gk).1 j hg
      · simp [hi] at hp

end MinMax

/-! ## End-to-end refinement -/

/-- Public operations of the tier layer. -/
inductive Op where
  | insert (k v : Nat)
  | remove (k : Nat)
  | get (k : Nat)
  | update (k : Nat) (f : Nat → Nat)
  | min
  | max
  | clear

inductive Out where
  | unit
  | val (o : Option Nat)
  | flag (b : Bool)
  | level (o : Option (Nat × Nat))

/-- One call of the Rust API on the model. `get`/`min`/`max` take `&self`
and leave the tier state unchanged. -/
def step (s : St) : Op → St × Out
  | .insert k v => (insert s k v, .unit)
  | .remove k => ((remove s k).1, .val (remove s k).2)
  | .get k => (s, .val (get s k))
  | .update k f => ((updateValue s k f).1, .flag (updateValue s k f).2)
  | .min => (s, .level (minOp s))
  | .max => (s, .level (maxOp s))
  | .clear => (init, .unit)

/-- Keys passed to `insert` are `u32`. -/
def Op.Ok : Op → Prop
  | .insert k _ => k ≤ U32_MAX
  | _ => True

/-- What a plain map does. -/
def specBook (b : Map) : Op → Map
  | .insert k v => specInsert b k v
  | .remove k => upd b k none
  | .get _ => b
  | .update k f => (specUpdate b k f).1
  | .min => b
  | .max => b
  | .clear => fun _ => none

/-- What a plain map answers. `SpecMin`/`SpecMax` pin the answer down
uniquely (`SpecMin.unique`, `SpecMax.unique`). -/
def OutOk (b : Map) : Op → Out → Prop
  | .insert _ _, o => o = .unit
  | .remove k, o => o = .val (b k)
  | .get k, o => o = .val (b k)
  | .update k f, o => o = .flag (specUpdate b k f).2
  | .min, .level r => SpecMin b r
  | .max, .level r => SpecMax b r
  | .clear, o => o = .unit
  | _, _ => False

theorem abs_init : abs init = fun _ => none := by funext k; simp [abs, init]

theorem step_correct {s : St} (h : Inv s) {op : Op} (hop : op.Ok) :
    Inv (step s op).1 ∧ abs (step s op).1 = specBook (abs s) op ∧ OutOk (abs s) op (step s op).2 := by
  cases op with
  | insert k v => exact ⟨(insert_correct h hop).1, (insert_correct h hop).2, rfl⟩
  | remove k => obtain ⟨a, b, c⟩ := remove_correct h k; exact ⟨a, b, by simp [step, OutOk, c]⟩
  | get k => exact ⟨h, rfl, by simp [step, OutOk, get_correct h k]⟩
  | update k f =>
    obtain ⟨a, b, c⟩ := updateValue_correct h k f; exact ⟨a, b, by simp [step, OutOk, c]⟩
  | min => exact ⟨h, rfl, minOp_correct h⟩
  | max => exact ⟨h, rfl, maxOp_correct h⟩
  | clear => exact ⟨inv_init, abs_init, rfl⟩

def run : St → List Op → St × List Out
  | s, [] => (s, [])
  | s, op :: ops => ((run (step s op).1 ops).1, (step s op).2 :: (run (step s op).1 ops).2)

def specRun (b : Map) : List Op → Map
  | [] => b
  | op :: ops => specRun (specBook b op) ops

def TraceOk : Map → List Op → List Out → Prop
  | _, [], [] => True
  | b, op :: ops, o :: os => OutOk b op o ∧ TraceOk (specBook b op) ops os
  | _, _, _ => False

theorem run_correct (ops : List Op) (hops : ∀ op ∈ ops, op.Ok) (s : St) (h : Inv s) :
    Inv (run s ops).1 ∧ abs (run s ops).1 = specRun (abs s) ops ∧
    TraceOk (abs s) ops (run s ops).2 := by
  induction ops generalizing s with
  | nil => exact ⟨h, rfl, trivial⟩
  | cons op ops ih =>
    obtain ⟨h1, h2, h3⟩ := step_correct h (hops op List.mem_cons_self)
    obtain ⟨i1, i2, i3⟩ := ih (fun o ho => hops o (List.mem_cons_of_mem _ ho)) _ h1
    refine ⟨i1, ?_, h3, ?_⟩
    · simp only [run, specRun]; rw [i2, h2]
    · rw [← h2]; exact i3

/-- **Headline.** For every sequence of API calls starting from `Glass::new()`,
every answer the two-tier implementation gives (`get`, `remove`'s return,
`update_value`'s flag, `min`, `max`) is exactly the answer a plain map would
give, the tier invariant holds throughout, and the final book is the plain
map's. Only `insert` keys need to be `u32` (as the Rust signature enforces). -/
theorem glass_refines_map (ops : List Op) (hops : ∀ op ∈ ops, op.Ok) :
    Inv (run init ops).1 ∧ abs (run init ops).1 = specRun (fun _ => none) ops ∧
    TraceOk (fun _ => none) ops (run init ops).2 := by
  have := run_correct ops hops init inv_init
  rwa [abs_init] at this

end Glass.Tiers
