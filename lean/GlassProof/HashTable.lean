import GlassProof.Basic

/-!
# The intrusive leaf hash table (paper §5.2)

Model of `ht_lookup` / `find_leaf` / `ht_insert` / `ht_remove`
(`src/lib.rs:620-721`).

**Modeled.** The leaf arena's hash-table fields are total functions on arena
indices: `htK` (`LeafNode.ht_k`), `next` (`ht_next`), `prev` (`ht_prev`), plus
the bucket heads `heads` (`ht_heads`). `u32` values are `Nat`s; `NULL`
(`u32::MAX`) is the list terminator and the `HT_ABSENT` sentinel,
`HT_UNKNOWN = u32::MAX - 1`. Each Rust function is transcribed statement by
statement, in order.

**Abstract state.** `C h : List Nat` is the chain of bucket `h`, head first.
A leaf is *live* iff it lies on some chain `h < HT_SIZE`.

**Representation invariant `Inv t C`.** Walking `next` from `heads h` visits
exactly `C h` and then `NULL`, and `prev` mirrors it (the head's `prev` is
`NULL`); chains have no duplicates; every chained leaf sits in the bucket of
its own key; chained indices are `< HT_UNKNOWN`; and partial keys are unique
among live leaves. `live_iff` derives that every live leaf lies in the chain
of its key's bucket, and `nodup` makes that exactly once.

**Assumed, not proved here.**
* `Inv` needs every live leaf index to be `< HT_UNKNOWN = 2^32 - 2`, so the
  leaf arena must hold at most `2^32 - 2` leaves. `find_leaf` depends on this:
  it reads `r < HT_UNKNOWN` as "found". In the crate a leaf is pushed onto the
  arena only when `leaf_free_list` is empty, so the arena never grows past the
  peak number of live leaves (at most `MAX_SIZE = 4096`, one key or more
  each). That arena and trie argument is outside this module.
* `trie_find_leaf` (the cold fallback, `src/lib.rs:652`) is an oracle with
  the contract "returns the live leaf whose partial key is `p`, if any"
  (`TrieExact`). Proving that is the trie's job.
* `ht_insert` is called only on a fresh leaf (not live) whose partial key is
  not live yet: `glass_insert` (`src/lib.rs:1588-1618`) calls it only when
  the trie slot for that partial key was empty. `ht_remove` is called only on
  a live leaf. Both are hypotheses of the preservation theorems.
-/

namespace Glass.HashTable

/-- `u32::MAX`: null index / chain terminator. -/
def NULL : Nat := U32_MAX
/-- `HT_ABSENT` (`src/lib.rs:76`). -/
def HT_ABSENT : Nat := U32_MAX
/-- `HT_UNKNOWN` (`src/lib.rs:77`). -/
def HT_UNKNOWN : Nat := U32_MAX - 1
/-- `HT_SIZE` (`src/lib.rs:53`). -/
def HT_SIZE : Nat := 4096
/-- `HT_MAX_LOOKUP_LEN` (`src/lib.rs:56`). -/
def HT_MAX_LOOKUP_LEN : Nat := 5

/-- `(partial_key as usize) & (HT_SIZE - 1)`. -/
def bucket (p : Nat) : Nat := p &&& (HT_SIZE - 1)

theorem bucket_eq_mod (p : Nat) : bucket p = p % HT_SIZE := by
  have : HT_SIZE = 2 ^ 12 := rfl
  unfold bucket; rw [this]; exact Nat.and_two_pow_sub_one_eq_mod p 12

theorem bucket_lt (p : Nat) : bucket p < HT_SIZE := by
  rw [bucket_eq_mod]; exact Nat.mod_lt _ (by decide)

theorem unknown_lt_null : HT_UNKNOWN < NULL := by decide
theorem absent_eq_null : HT_ABSENT = NULL := rfl
theorem unknown_ne_absent : HT_UNKNOWN ≠ HT_ABSENT := by decide

/-- The hash-table view of the leaf arena. -/
structure HT where
  heads : Nat → Nat
  htK : Nat → Nat
  next : Nat → Nat
  prev : Nat → Nat

/-- Point update of an arena field (`arena[a].f = b`). -/
def upd (f : Nat → Nat) (a b : Nat) : Nat → Nat := fun x => if x = a then b else f x

@[simp] theorem upd_self (f : Nat → Nat) (a b : Nat) : upd f a b a = b := by simp [upd]
@[simp] theorem upd_other (f : Nat → Nat) {a x : Nat} (b : Nat) (h : x ≠ a) :
    upd f a b x = f x := by simp [upd, h]

/-! ## Transcriptions -/

/-- The bounded probe loop of `ht_lookup` (`src/lib.rs:628-644`), with
`fuel = HT_MAX_LOOKUP_LEN - lookups`:
```
while curr != u32::MAX && lookups < HT_MAX_LOOKUP_LEN {
    if leaf.ht_k == partial_key { return curr; }
    curr = leaf.ht_next; lookups += 1;
}
if curr == u32::MAX { HT_ABSENT } else { HT_UNKNOWN }
``` -/
def walk (t : HT) (p : Nat) : Nat → Nat → Nat
  | 0, curr => if curr = NULL then HT_ABSENT else HT_UNKNOWN
  | fuel + 1, curr =>
    if curr = NULL then HT_ABSENT
    else if t.htK curr = p then curr
    else walk t p fuel (t.next curr)

/-- `ht_lookup` (`src/lib.rs:625-650`). -/
def htLookup (t : HT) (p : Nat) : Nat := walk t p HT_MAX_LOOKUP_LEN (t.heads (bucket p))

/-- `find_leaf` (`src/lib.rs:667-678`); `trieFind` stands for `trie_find_leaf`. -/
def findLeaf (t : HT) (trieFind : Nat → Option Nat) (p : Nat) : Option Nat :=
  let r := htLookup t p
  if r < HT_UNKNOWN then some r
  else if r = HT_ABSENT then none
  else trieFind p

/-- `ht_insert` (`src/lib.rs:680-695`), statement by statement. -/
def htInsert (t : HT) (i p : Nat) : HT :=
  let h := bucket p
  let oldHead := t.heads h
  -- leaf.ht_k = partial_key; leaf.ht_next = old_head; leaf.ht_prev = u32::MAX;
  let t1 := { t with htK := upd t.htK i p, next := upd t.next i oldHead,
                     prev := upd t.prev i NULL }
  -- if old_head != u32::MAX { arena[old_head].ht_prev = leaf_idx; }
  let t2 := if oldHead ≠ NULL then { t1 with prev := upd t1.prev oldHead i } else t1
  -- heads[h] = leaf_idx;
  { t2 with heads := upd t2.heads h i }

/-- `ht_remove` (`src/lib.rs:697-721`), statement by statement. -/
def htRemove (t : HT) (i : Nat) : HT :=
  let prv := t.prev i
  let nxt := t.next i
  let p := t.htK i
  -- leaf.ht_k = u32::MAX; leaf.ht_next = u32::MAX; leaf.ht_prev = u32::MAX;
  let t1 := { t with htK := upd t.htK i NULL, next := upd t.next i NULL,
                     prev := upd t.prev i NULL }
  -- if prev != MAX { arena[prev].ht_next = next } else { heads[h] = next }
  let t2 := if prv ≠ NULL then { t1 with next := upd t1.next prv nxt }
            else { t1 with heads := upd t1.heads (bucket p) nxt }
  -- if next != MAX { arena[next].ht_prev = prev }
  if nxt ≠ NULL then { t2 with prev := upd t2.prev nxt prv } else t2

/-! ## Doubly-linked segments -/

/-- `Seg next prev prv l term`: `l` is a doubly-linked segment whose first
element's `prev` is `prv`, whose consecutive elements are linked both ways,
and whose last element's `next` is `term`. -/
def Seg (next prev : Nat → Nat) : Nat → List Nat → Nat → Prop
  | _, [], _ => True
  | prv, a :: rest, term => prev a = prv ∧ next a = rest.headD term ∧ Seg next prev a rest term

/-- Last element of a list, or `d` if empty. -/
def lastD : List Nat → Nat → Nat
  | [], d => d
  | a :: rest, _ => lastD rest a

theorem headD_append (l₁ l₂ : List Nat) (d : Nat) :
    (l₁ ++ l₂).headD d = l₁.headD (l₂.headD d) := by
  cases l₁ <;> rfl

theorem lastD_append_single (l : List Nat) (x d : Nat) : lastD (l ++ [x]) d = x := by
  induction l generalizing d with
  | nil => rfl
  | cons a rest ih => exact ih a

theorem lastD_mem_or (l : List Nat) (d : Nat) : lastD l d = d ∨ lastD l d ∈ l := by
  induction l generalizing d with
  | nil => exact Or.inl rfl
  | cons a rest ih =>
    rcases ih a with h | h
    · exact Or.inr (by simp [lastD, h])
    · exact Or.inr (by simp [lastD, h])

theorem seg_append (next prev : Nat → Nat) (l₁ l₂ : List Nat) (prv term : Nat) :
    Seg next prev prv (l₁ ++ l₂) term ↔
      Seg next prev prv l₁ (l₂.headD term) ∧ Seg next prev (lastD l₁ prv) l₂ term := by
  induction l₁ generalizing prv with
  | nil => simp [Seg, lastD]
  | cons a rest ih =>
    simp only [List.cons_append, Seg, lastD, ih, headD_append]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h2, h3⟩, h4⟩
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨h1, h2, h3, h4⟩

/-- Frame rule: a segment only depends on the links of its own elements. -/
theorem seg_frame {next prev next' prev' : Nat → Nat} {prv term : Nat} :
    ∀ {l : List Nat}, Seg next prev prv l term →
      (∀ a ∈ l, next' a = next a ∧ prev' a = prev a) → Seg next' prev' prv l term := by
  intro l
  induction l generalizing prv with
  | nil => intros; trivial
  | cons a rest ih =>
    rintro ⟨h1, h2, h3⟩ hag
    have ha := hag a (by simp)
    refine ⟨by rw [ha.2, h1], by rw [ha.1, h2], ih h3 fun b hb => hag b (by simp [hb])⟩

/-- A segment ending in `NULL` is walked by `next` from its head. -/
theorem seg_cons_next {next prev : Nat → Nat} {prv a : Nat} {rest : List Nat} {term : Nat}
    (h : Seg next prev prv (a :: rest) term) : next a = rest.headD term := h.2.1

/-! ## Representation invariant -/

/-- A leaf is live iff it is chained in some bucket. -/
def Live (C : Nat → List Nat) (i : Nat) : Prop := ∃ h, h < HT_SIZE ∧ i ∈ C h

structure Inv (t : HT) (C : Nat → List Nat) : Prop where
  heads_eq : ∀ h, h < HT_SIZE → t.heads h = (C h).headD NULL
  linked : ∀ h, h < HT_SIZE → Seg t.next t.prev NULL (C h) NULL
  nodup : ∀ h, h < HT_SIZE → (C h).Nodup
  bucket_ok : ∀ h, h < HT_SIZE → ∀ i ∈ C h, bucket (t.htK i) = h
  idx_lt : ∀ h, h < HT_SIZE → ∀ i ∈ C h, i < HT_UNKNOWN
  key_unique : ∀ i j, Live C i → Live C j → t.htK i = t.htK j → i = j

/-- Every live leaf lies on the chain of its own key's bucket (and, by
`Inv.nodup`, exactly once). -/
theorem live_iff {t : HT} {C : Nat → List Nat} (hI : Inv t C) (i : Nat) :
    Live C i ↔ i ∈ C (bucket (t.htK i)) := by
  constructor
  · rintro ⟨h, hh, hi⟩
    rw [hI.bucket_ok h hh i hi]; exact hi
  · intro hi; exact ⟨_, bucket_lt _, hi⟩

/-- A live leaf lies on exactly one chain, the one of its key's bucket (and
`Inv.nodup` makes it appear there once). -/
theorem live_chain_unique {t : HT} {C : Nat → List Nat} (hI : Inv t C) {i h : Nat}
    (hi : Live C i) (hh : h < HT_SIZE) : i ∈ C h ↔ h = bucket (t.htK i) :=
  ⟨fun hm => (hI.bucket_ok h hh i hm).symm, fun e => e ▸ (live_iff hI i).1 hi⟩

theorem live_lt {t : HT} {C : Nat → List Nat} (hI : Inv t C) {i : Nat} (hi : Live C i) :
    i < HT_UNKNOWN := by
  obtain ⟨h, hh, hm⟩ := hi; exact hI.idx_lt h hh i hm

/-- A leaf lies on at most one chain. -/
theorem chains_disjoint {t : HT} {C : Nat → List Nat} (hI : Inv t C) {h h' i : Nat}
    (hh : h < HT_SIZE) (hh' : h' < HT_SIZE) (hi : i ∈ C h) (hi' : i ∈ C h') : h = h' := by
  rw [← hI.bucket_ok h hh i hi, hI.bucket_ok h' hh' i hi']

/-- The empty table (`Glass::new`/`clear`: `ht_heads.fill(u32::MAX)`). -/
theorem inv_empty (t : HT) (hheads : ∀ h, h < HT_SIZE → t.heads h = NULL) :
    Inv t (fun _ => []) where
  heads_eq h hh := by simp [hheads h hh]
  linked _ _ := trivial
  nodup _ _ := List.nodup_nil
  bucket_ok _ _ _ hi := by simp at hi
  idx_lt _ _ _ hi := by simp at hi
  key_unique i _ hi := by obtain ⟨_, _, hm⟩ := hi; simp at hm

/-! ## (1) Lookup soundness -/

/-- The probe loop run on a segment: it returns a chained leaf with the
key, or `HT_ABSENT` after scanning the whole segment without a match, or
`HT_UNKNOWN` when the segment is longer than the fuel. -/
theorem walk_cases (t : HT) (p : Nat) :
    ∀ (fuel : Nat) (l : List Nat) (prv : Nat), Seg t.next t.prev prv l NULL →
      (∀ i ∈ l, i ≠ NULL) →
      let r := walk t p fuel (l.headD NULL)
      (r ∈ l ∧ t.htK r = p) ∨ (r = HT_ABSENT ∧ ∀ i ∈ l, t.htK i ≠ p) ∨
        (r = HT_UNKNOWN ∧ fuel < l.length) := by
  intro fuel
  induction fuel with
  | zero =>
    intro l prv _ hne
    cases l with
    | nil => simp [walk]
    | cons a rest =>
      have : a ≠ NULL := hne a (by simp)
      simp [walk, this]
  | succ n ih =>
    intro l prv hseg hne
    cases l with
    | nil => simp [walk]
    | cons a rest =>
      have ha : a ≠ NULL := hne a (by simp)
      simp only [List.headD_cons]
      by_cases hk : t.htK a = p
      · left; simp [walk, ha, hk]
      · have hnext : t.next a = rest.headD NULL := hseg.2.1
        have hw : walk t p (n + 1) a = walk t p n (rest.headD NULL) := by
          simp [walk, ha, hk, hnext]
        rw [hw]
        rcases ih rest a hseg.2.2 (fun i hi => hne i (by simp [hi])) with h | h | h
        · left; exact ⟨List.mem_cons_of_mem _ h.1, h.2⟩
        · right; left
          refine ⟨h.1, ?_⟩
          intro i hi
          simp only [List.mem_cons] at hi
          rcases hi with rfl | hi
          · exact hk
          · exact h.2 i hi
        · right; right; exact ⟨h.1, by simp; omega⟩

theorem htLookup_cases {t : HT} {C : Nat → List Nat} (hI : Inv t C) (p : Nat) :
    let r := htLookup t p
    (r ∈ C (bucket p) ∧ t.htK r = p) ∨ (r = HT_ABSENT ∧ ∀ i ∈ C (bucket p), t.htK i ≠ p) ∨
      (r = HT_UNKNOWN ∧ HT_MAX_LOOKUP_LEN < (C (bucket p)).length) := by
  have hb := bucket_lt p
  unfold htLookup
  rw [hI.heads_eq _ hb]
  exact walk_cases t p _ _ _ (hI.linked _ hb) fun i hi =>
    Nat.ne_of_lt (Nat.lt_trans (hI.idx_lt _ hb i hi) unknown_lt_null)

/-- (1a) A found index is a live leaf carrying the key. -/
theorem htLookup_found {t : HT} {C : Nat → List Nat} (hI : Inv t C) (p : Nat)
    (hr : htLookup t p < HT_UNKNOWN) : Live C (htLookup t p) ∧ t.htK (htLookup t p) = p := by
  rcases htLookup_cases hI p with h | h | h
  · exact ⟨⟨_, bucket_lt p, h.1⟩, h.2⟩
  · exfalso; rw [h.1] at hr; exact absurd hr (by decide)
  · exfalso; rw [h.1] at hr; exact Nat.lt_irrefl _ hr

/-- (1b) "Absent" is authoritative (paper §5.2): no live leaf has the key. -/
theorem htLookup_absent {t : HT} {C : Nat → List Nat} (hI : Inv t C) (p : Nat)
    (hr : htLookup t p = HT_ABSENT) : ∀ i, Live C i → t.htK i ≠ p := by
  intro i hi hk
  rcases htLookup_cases hI p with h | h | h
  · have := hI.idx_lt _ (bucket_lt p) _ h.1
    rw [hr] at this; exact absurd this (by decide)
  · rw [live_iff hI, hk] at hi; exact h.2 i hi hk
  · rw [hr] at h; exact unknown_ne_absent h.1.symm

/-- (1c) "Unknown" only happens when the chain is longer than the probe
bound. -/
theorem htLookup_unknown {t : HT} {C : Nat → List Nat} (hI : Inv t C) (p : Nat)
    (hr : htLookup t p = HT_UNKNOWN) : HT_MAX_LOOKUP_LEN < (C (bucket p)).length := by
  rcases htLookup_cases hI p with h | h | h
  · have := hI.idx_lt _ (bucket_lt p) _ h.1
    rw [hr] at this; exact absurd this (Nat.lt_irrefl _)
  · rw [hr] at h; exact absurd h.1 unknown_ne_absent
  · exact h.2

/-! ## (2) `find_leaf` is exact -/

/-- Contract of `trie_find_leaf` (the trie descent), assumed here. -/
def TrieExact (t : HT) (C : Nat → List Nat) (trieFind : Nat → Option Nat) : Prop :=
  ∀ p i, trieFind p = some i ↔ (Live C i ∧ t.htK i = p)

/-- (2) `find_leaf p` returns exactly the live leaf whose partial key is `p`. -/
theorem findLeaf_spec {t : HT} {C : Nat → List Nat} (hI : Inv t C)
    {trieFind : Nat → Option Nat} (hT : TrieExact t C trieFind) (p i : Nat) :
    findLeaf t trieFind p = some i ↔ (Live C i ∧ t.htK i = p) := by
  unfold findLeaf
  simp only
  by_cases h1 : htLookup t p < HT_UNKNOWN
  · rw [if_pos h1]
    have hf := htLookup_found hI p h1
    constructor
    · rintro ⟨⟩; exact hf
    · rintro ⟨hl, hk⟩
      exact congrArg some (hI.key_unique _ _ hf.1 hl (by rw [hf.2, hk]))
  · rw [if_neg h1]
    by_cases h2 : htLookup t p = HT_ABSENT
    · rw [if_pos h2]
      simp only [reduceCtorEq, false_iff, not_and]
      exact fun hl hk => htLookup_absent hI p h2 i hl hk
    · rw [if_neg h2]; exact hT p i

/-- (2') `find_leaf p = none` iff no live leaf has partial key `p`. -/
theorem findLeaf_none {t : HT} {C : Nat → List Nat} (hI : Inv t C)
    {trieFind : Nat → Option Nat} (hT : TrieExact t C trieFind) (p : Nat) :
    findLeaf t trieFind p = none ↔ ∀ i, Live C i → t.htK i ≠ p := by
  constructor
  · intro h i hl hk
    have := (findLeaf_spec hI hT p i).2 ⟨hl, hk⟩
    rw [h] at this; exact absurd this (by simp)
  · intro h
    cases hf : findLeaf t trieFind p with
    | none => rfl
    | some i =>
      have := (findLeaf_spec hI hT p i).1 hf
      exact absurd this.2 (h i this.1)

/-! ## Field-level effects of `ht_insert` / `ht_remove` -/

section fields
variable (t : HT) (i p : Nat)

theorem ins_htK (c : Nat) : (htInsert t i p).htK c = if c = i then p else t.htK c := by
  unfold htInsert; dsimp only; split <;> simp [upd]

theorem ins_next (c : Nat) :
    (htInsert t i p).next c = if c = i then t.heads (bucket p) else t.next c := by
  unfold htInsert; dsimp only; split <;> simp [upd]

theorem ins_heads (h : Nat) :
    (htInsert t i p).heads h = if h = bucket p then i else t.heads h := by
  unfold htInsert; dsimp only; split <;> simp [upd]

theorem ins_prev_frame {c : Nat} (hi : c ≠ i) (ho : c ≠ t.heads (bucket p)) :
    (htInsert t i p).prev c = t.prev c := by
  unfold htInsert; dsimp only; split <;> simp [upd, hi, ho]

theorem ins_prev_self (hio : i ≠ t.heads (bucket p)) : (htInsert t i p).prev i = NULL := by
  unfold htInsert; dsimp only; split <;> simp [upd, hio]

theorem ins_prev_head (ho : t.heads (bucket p) ≠ NULL) :
    (htInsert t i p).prev (t.heads (bucket p)) = i := by
  unfold htInsert; dsimp only; simp [ho, upd]

theorem rem_htK (c : Nat) : (htRemove t i).htK c = if c = i then NULL else t.htK c := by
  unfold htRemove; dsimp only; split <;> split <;> simp [upd]

theorem rem_next_frame {c : Nat} (hi : c ≠ i) (hp : c ≠ t.prev i) :
    (htRemove t i).next c = t.next c := by
  unfold htRemove; dsimp only; split <;> split <;> simp [upd, hi, hp]

theorem rem_prev_frame {c : Nat} (hi : c ≠ i) (hn : c ≠ t.next i) :
    (htRemove t i).prev c = t.prev c := by
  unfold htRemove; dsimp only; split <;> split <;> simp [upd, hi, hn]

theorem rem_next_prv (hp : t.prev i ≠ NULL) :
    (htRemove t i).next (t.prev i) = t.next i := by
  unfold htRemove; dsimp only; split <;> simp_all [upd]

theorem rem_prev_nxt (hn : t.next i ≠ NULL) :
    (htRemove t i).prev (t.next i) = t.prev i := by
  unfold htRemove; dsimp only; simp [upd, hn]

theorem rem_heads_other {h : Nat} (hh : h ≠ bucket (t.htK i)) :
    (htRemove t i).heads h = t.heads h := by
  unfold htRemove; dsimp only; split <;> split <;> simp [upd, hh]

theorem rem_heads_prv (hp : t.prev i ≠ NULL) (h : Nat) : (htRemove t i).heads h = t.heads h := by
  unfold htRemove; dsimp only; split <;> simp_all

theorem rem_heads_null (hp : t.prev i = NULL) :
    (htRemove t i).heads (bucket (t.htK i)) = t.next i := by
  unfold htRemove; dsimp only; split <;> simp [hp, upd]

end fields

theorem lastD_mem_cons (a : Nat) (rest : List Nat) (d : Nat) : lastD (a :: rest) d ∈ a :: rest := by
  rcases lastD_mem_or rest a with h | h
  · simp [lastD, h]
  · simp [lastD, h]

theorem chain_ne_null {t : HT} {C : Nat → List Nat} (hI : Inv t C) {h c : Nat}
    (hh : h < HT_SIZE) (hc : c ∈ C h) : c ≠ NULL :=
  Nat.ne_of_lt (Nat.lt_trans (hI.idx_lt h hh c hc) unknown_lt_null)

/-! ## (3) `ht_insert` preserves the invariant -/

/-- (3) Inserting a fresh leaf `i` with an unused partial key `p` pushes it
onto the front of `p`'s chain; the invariant is preserved, `i` becomes the
only new live leaf, and no other leaf's key changes. -/
theorem htInsert_inv {t : HT} {C : Nat → List Nat} (hI : Inv t C) {i p : Nat}
    (hfresh : ¬ Live C i) (hidx : i < HT_UNKNOWN) (hkey : ∀ j, Live C j → t.htK j ≠ p) :
    let C' := fun h => if h = bucket p then i :: C h else C h
    Inv (htInsert t i p) C' ∧ (∀ j, Live C' j ↔ Live C j ∨ j = i) ∧
      (htInsert t i p).htK i = p ∧ ∀ j, j ≠ i → (htInsert t i p).htK j = t.htK j := by
  intro C'
  have hb := bucket_lt p
  have hiC : ∀ h, h < HT_SIZE → i ∉ C h := fun h hh hm => hfresh ⟨h, hh, hm⟩
  have hiN : i ≠ NULL := Nat.ne_of_lt (Nat.lt_trans hidx unknown_lt_null)
  -- the old head is `NULL` or a member of `C (bucket p)`
  have hoh : t.heads (bucket p) = NULL ∨ t.heads (bucket p) ∈ C (bucket p) := by
    rw [hI.heads_eq _ hb]
    cases C (bucket p) with
    | nil => exact Or.inl rfl
    | cons a _ => exact Or.inr (by simp)
  have hio : i ≠ t.heads (bucket p) := by
    rcases hoh with h | h
    · rw [h]; exact hiN
    · exact fun e => hiC _ hb (e ▸ h)
  have hK : ∀ j, j ≠ i → (htInsert t i p).htK j = t.htK j := by
    intro j hj; rw [ins_htK]; simp [hj]
  -- elements of any chain other than `i` and the old head keep their links
  have hframe : ∀ c, c ≠ i → c ≠ t.heads (bucket p) →
      (htInsert t i p).next c = t.next c ∧ (htInsert t i p).prev c = t.prev c := by
    intro c hci hco
    exact ⟨by rw [ins_next]; simp [hci], ins_prev_frame t i p hci hco⟩
  have hLive : ∀ j, Live C' j ↔ Live C j ∨ j = i := by
    intro j
    constructor
    · rintro ⟨h, hh, hm⟩
      by_cases e : h = bucket p
      · simp only [C', e, if_pos] at hm
        rcases List.mem_cons.1 hm with rfl | hm
        · exact Or.inr rfl
        · exact Or.inl ⟨_, hb, hm⟩
      · simp only [C', e, if_neg, not_false_eq_true] at hm
        exact Or.inl ⟨h, hh, hm⟩
    · rintro (⟨h, hh, hm⟩ | rfl)
      · by_cases e : h = bucket p
        · subst e; exact ⟨_, hh, by simp [C', hm]⟩
        · exact ⟨h, hh, by simp [C', e, hm]⟩
      · exact ⟨_, hb, by simp [C']⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hLive, by rw [ins_htK]; simp, hK⟩
  · -- heads
    intro h hh
    rw [ins_heads]
    by_cases e : h = bucket p
    · simp [C', e]
    · simp [C', e, hI.heads_eq h hh]
  · -- linked
    intro h hh
    by_cases e : h = bucket p
    · subst e
      simp only [C', if_pos]
      have hseg := hI.linked _ hb
      have hnd := hI.nodup _ hb
      refine ⟨ins_prev_self t i p hio, ?_, ?_⟩
      · rw [ins_next]; simp [hI.heads_eq _ hb]
      · -- the old chain, now hanging off `i`
        revert hseg hnd
        cases hc : C (bucket p) with
        | nil => intros; trivial
        | cons a rest =>
          intro hseg hnd
          have ha : a ∈ C (bucket p) := by rw [hc]; simp
          have haN : a ≠ NULL := chain_ne_null hI hb ha
          have hai : a ≠ i := fun e => hiC _ hb (e ▸ ha)
          have hhead : t.heads (bucket p) = a := by rw [hI.heads_eq _ hb, hc]; rfl
          refine ⟨?_, ?_, ?_⟩
          · have := ins_prev_head t i p (by rw [hhead]; exact haN)
            rwa [hhead] at this
          · rw [ins_next]; simp [hai, hseg.2.1]
          · refine seg_frame hseg.2.2 fun c hcm => hframe c ?_ ?_
            · exact fun e => hiC _ hb (by rw [hc]; exact e ▸ List.mem_cons_of_mem _ hcm)
            · rw [hhead]; intro e; subst e
              exact (List.nodup_cons.1 hnd).1 hcm
    · simp only [C', e, if_neg, not_false_eq_true]
      refine seg_frame (hI.linked h hh) fun c hcm => hframe c ?_ ?_
      · exact fun e' => hiC h hh (e' ▸ hcm)
      · intro e'
        rcases hoh with h0 | h0
        · exact chain_ne_null hI hh hcm (e'.trans h0)
        · exact e (chains_disjoint hI hh hb hcm (e' ▸ h0))
  · -- nodup
    intro h hh
    by_cases e : h = bucket p
    · subst e; simp only [C', if_pos]
      exact List.nodup_cons.2 ⟨hiC _ hb, hI.nodup _ hb⟩
    · simp only [C', e, if_neg, not_false_eq_true]; exact hI.nodup h hh
  · -- bucket_ok
    intro h hh c hc
    by_cases e : h = bucket p
    · subst e
      simp only [C', if_pos, List.mem_cons] at hc
      rcases hc with rfl | hc
      · rw [ins_htK]; simp
      · have hci : c ≠ i := fun e' => hiC _ hb (e' ▸ hc)
        rw [hK c hci]; exact hI.bucket_ok _ hb c hc
    · simp only [C', e, if_neg, not_false_eq_true] at hc
      have hci : c ≠ i := fun e' => hiC h hh (e' ▸ hc)
      rw [hK c hci]; exact hI.bucket_ok h hh c hc
  · -- idx_lt
    intro h hh c hc
    by_cases e : h = bucket p
    · subst e
      simp only [C', if_pos, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hidx
      · exact hI.idx_lt _ hb c hc
    · simp only [C', e, if_neg, not_false_eq_true] at hc
      exact hI.idx_lt h hh c hc
  · -- key_unique
    intro a c ha hc hk
    rcases (hLive a).1 ha with ha | ea <;> rcases (hLive c).1 hc with hc | ec
    · have hai : a ≠ i := fun e => hfresh (e ▸ ha)
      have hci : c ≠ i := fun e => hfresh (e ▸ hc)
      rw [hK a hai, hK c hci] at hk
      exact hI.key_unique a c ha hc hk
    · have hai : a ≠ i := fun e => hfresh (e ▸ ha)
      rw [hK a hai, ec, ins_htK] at hk; simp at hk
      exact absurd hk (hkey a ha)
    · have hci : c ≠ i := fun e => hfresh (e ▸ hc)
      rw [hK c hci, ea, ins_htK] at hk; simp at hk
      exact absurd hk.symm (hkey c hc)
    · rw [ea, ec]

/-! ## (4) `ht_remove` preserves the invariant -/

/-- (4) Removing a live leaf `i` unlinks it from its chain (the chain becomes
`erase i`); the invariant is preserved, exactly `i` stops being live, and no
other leaf's key changes. -/
theorem htRemove_inv {t : HT} {C : Nat → List Nat} (hI : Inv t C) {i : Nat}
    (hlive : Live C i) :
    let C' := fun h => if h = bucket (t.htK i) then (C h).erase i else C h
    Inv (htRemove t i) C' ∧ (∀ j, Live C' j ↔ Live C j ∧ j ≠ i) ∧
      ∀ j, j ≠ i → (htRemove t i).htK j = t.htK j := by
  intro C'
  have hb : bucket (t.htK i) < HT_SIZE := bucket_lt _
  have hiC : i ∈ C (bucket (t.htK i)) := (live_iff hI i).1 hlive
  obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hiC
  have hnd := hI.nodup _ hb
  rw [hsplit] at hnd
  obtain ⟨hndpre, hndpi, hdisj⟩ := List.nodup_append.1 hnd
  have hipost : i ∉ post := (List.nodup_cons.1 hndpi).1
  have hndpost : post.Nodup := (List.nodup_cons.1 hndpi).2
  have hipre : i ∉ pre := fun h => hdisj i h i (by simp) rfl
  have hpp : ∀ a ∈ pre, ∀ c ∈ post, a ≠ c := fun a ha c hc => hdisj a ha c (by simp [hc])
  have hmemB : ∀ c, c ∈ pre ∨ c ∈ post → c ∈ C (bucket (t.htK i)) := by
    intro c hc; rw [hsplit]; rcases hc with h | h <;> simp [h]
  -- the old links around `i`
  have hseg := hI.linked _ hb
  rw [hsplit, seg_append] at hseg
  obtain ⟨hsegpre, hprevi, hnexti, hsegpost⟩ := hseg
  simp only [List.headD_cons] at hsegpre
  have herase : (C (bucket (t.htK i))).erase i = pre ++ post := by
    rw [hsplit, List.erase_append_right _ hipre, List.erase_cons_head]
  -- `prev i` is `NULL` (and `pre = []`) or the last of `pre`; dually `next i`
  have hprvcases : (t.prev i = NULL ∧ pre = []) ∨ t.prev i ∈ pre := by
    rw [hprevi]
    cases pre with
    | nil => exact Or.inl ⟨rfl, rfl⟩
    | cons a r => exact Or.inr (lastD_mem_cons a r NULL)
  have hnxtcases : (t.next i = NULL ∧ post = []) ∨ t.next i ∈ post := by
    rw [hnexti]
    cases post with
    | nil => exact Or.inl ⟨rfl, rfl⟩
    | cons a r => exact Or.inr (by simp)
  have neq_prv : ∀ c, c ≠ NULL → c ∉ pre → c ≠ t.prev i := by
    intro c hc hcp e
    rcases hprvcases with ⟨h0, _⟩ | h0
    · exact hc (e.trans h0)
    · exact hcp (e ▸ h0)
  have neq_nxt : ∀ c, c ≠ NULL → c ∉ post → c ≠ t.next i := by
    intro c hc hcp e
    rcases hnxtcases with ⟨h0, _⟩ | h0
    · exact hc (e.trans h0)
    · exact hcp (e ▸ h0)
  have hframe : ∀ c, c ≠ i → c ≠ t.prev i → c ≠ t.next i →
      (htRemove t i).next c = t.next c ∧ (htRemove t i).prev c = t.prev c :=
    fun c hi hp hn => ⟨rem_next_frame t i hi hp, rem_prev_frame t i hi hn⟩
  have hK : ∀ j, j ≠ i → (htRemove t i).htK j = t.htK j := by
    intro j hj; rw [rem_htK]; simp [hj]
  -- a leaf on another chain is none of `i`, `prev i`, `next i`
  have hother : ∀ h, h < HT_SIZE → h ≠ bucket (t.htK i) → ∀ c ∈ C h,
      c ≠ i ∧ c ≠ t.prev i ∧ c ≠ t.next i := by
    intro h hh e c hc
    have hcB : c ∉ C (bucket (t.htK i)) := fun hm => e (chains_disjoint hI hh hb hc hm)
    have hcN := chain_ne_null hI hh hc
    exact ⟨fun e' => hcB (e' ▸ hiC), neq_prv c hcN (fun hm => hcB (hmemB c (Or.inl hm))),
      neq_nxt c hcN (fun hm => hcB (hmemB c (Or.inr hm)))⟩
  have hmem' : ∀ h, h < HT_SIZE → ∀ c ∈ C' h, c ∈ C h ∧ c ≠ i := by
    intro h hh c hc
    by_cases e : h = bucket (t.htK i)
    · subst e
      simp only [C', if_pos] at hc
      exact ((List.Nodup.mem_erase_iff (hI.nodup _ hb)).1 hc).symm
    · simp only [C', e, if_neg, not_false_eq_true] at hc
      exact ⟨hc, (hother h hh e c hc).1⟩
  have hLive : ∀ j, Live C' j ↔ Live C j ∧ j ≠ i := by
    intro j
    constructor
    · rintro ⟨h, hh, hm⟩
      obtain ⟨h1, h2⟩ := hmem' h hh j hm
      exact ⟨⟨h, hh, h1⟩, h2⟩
    · rintro ⟨⟨h, hh, hm⟩, hji⟩
      refine ⟨h, hh, ?_⟩
      by_cases e : h = bucket (t.htK i)
      · subst e
        simp only [C', if_pos]
        exact (List.Nodup.mem_erase_iff (hI.nodup _ hb)).2 ⟨hji, hm⟩
      · simp only [C', e, if_neg, not_false_eq_true]; exact hm
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hLive, hK⟩
  · -- heads
    intro h hh
    by_cases e : h = bucket (t.htK i)
    · subst e
      simp only [C', if_pos]
      rw [herase]
      rcases hprvcases with ⟨hp0, hpre⟩ | hpin
      · subst hpre
        rw [rem_heads_null t i hp0, hnexti]; rfl
      · have hpN : t.prev i ≠ NULL := chain_ne_null hI hb (hmemB _ (Or.inl hpin))
        rw [rem_heads_prv t i hpN, hI.heads_eq _ hb, hsplit]
        cases pre with
        | nil => simp at hpin
        | cons a r => rfl
    · simp only [C', e, if_neg, not_false_eq_true]
      rw [rem_heads_other t i e, hI.heads_eq h hh]
  · -- linked
    intro h hh
    by_cases e : h = bucket (t.htK i)
    · subst e
      simp only [C', if_pos]
      rw [herase, seg_append]
      constructor
      · -- the part before `i`: its last element now points past `i`
        rcases List.eq_nil_or_concat pre with hpre | ⟨pre', x, hpre⟩
        · subst hpre; trivial
        · rw [List.concat_eq_append] at hpre
          subst hpre
          have hx : x ∈ pre' ++ [x] := by simp
          have hxN : x ≠ NULL := chain_ne_null hI hb (hmemB x (Or.inl hx))
          have hxprv : t.prev i = x := by rw [hprevi, lastD_append_single]
          have hxpost : x ∉ post := fun hm => hpp x hx x hm rfl
          rw [seg_append] at hsegpre ⊢
          obtain ⟨hsegpre', hxprev, _, _⟩ := hsegpre
          simp only [List.headD_cons] at hsegpre' ⊢
          obtain ⟨hndpre', _, hdisj'⟩ := List.nodup_append.1 hndpre
          refine ⟨seg_frame hsegpre' fun c hc => hframe c ?_ ?_ ?_, ?_, ?_, trivial⟩
          · exact fun e' => hipre (e' ▸ by simp [hc])
          · rw [hxprv]; exact fun e' => hdisj' c hc x (by simp) e'
          · exact neq_nxt c (chain_ne_null hI hb (hmemB c (Or.inl (by simp [hc]))))
              (fun hm => hpp c (by simp [hc]) c hm rfl)
          · rw [rem_prev_frame t i (fun e' => hipre (e' ▸ hx)) (neq_nxt x hxN hxpost), hxprev]
          · have := rem_next_prv t i (by rw [hxprv]; exact hxN)
            rw [hxprv] at this
            rw [this, hnexti]; rfl
      · -- the part after `i`: its first element now points back past `i`
        cases post with
        | nil => trivial
        | cons y post'' =>
          obtain ⟨hyprev, hynext, hsegpost''⟩ := hsegpost
          have hy : y ∈ y :: post'' := by simp
          have hyN : y ≠ NULL := chain_ne_null hI hb (hmemB y (Or.inr hy))
          have hynxt : t.next i = y := by rw [hnexti]; rfl
          have hypre : y ∉ pre := fun hm => hpp y hm y hy rfl
          have hnd'' := List.nodup_cons.1 hndpost
          refine ⟨?_, ?_, seg_frame hsegpost'' fun c hc => hframe c ?_ ?_ ?_⟩
          · have := rem_prev_nxt t i (by rw [hynxt]; exact hyN)
            rw [hynxt] at this
            rw [this, hprevi]
          · rw [rem_next_frame t i (fun e' => hipost (e' ▸ hy)) (neq_prv y hyN hypre), hynext]
          · exact fun e' => hipost (e' ▸ by simp [hc])
          · exact neq_prv c (chain_ne_null hI hb (hmemB c (Or.inr (by simp [hc]))))
              (fun hm => hpp c hm c (by simp [hc]) rfl)
          · rw [hynxt]; exact fun e' => hnd''.1 (e' ▸ hc)
    · simp only [C', e, if_neg, not_false_eq_true]
      exact seg_frame (hI.linked h hh) fun c hc =>
        let ⟨h1, h2, h3⟩ := hother h hh e c hc
        hframe c h1 h2 h3
  · -- nodup
    intro h hh
    by_cases e : h = bucket (t.htK i)
    · subst e; simp only [C', if_pos]; exact (hI.nodup _ hb).erase i
    · simp only [C', e, if_neg, not_false_eq_true]; exact hI.nodup h hh
  · -- bucket_ok
    intro h hh c hc
    obtain ⟨h1, h2⟩ := hmem' h hh c hc
    rw [hK c h2]; exact hI.bucket_ok h hh c h1
  · -- idx_lt
    intro h hh c hc
    exact hI.idx_lt h hh c (hmem' h hh c hc).1
  · -- key_unique
    intro a c ha hc hk
    obtain ⟨ha, hai⟩ := (hLive a).1 ha
    obtain ⟨hc, hci⟩ := (hLive c).1 hc
    rw [hK a hai, hK c hci] at hk
    exact hI.key_unique a c ha hc hk

end Glass.HashTable
