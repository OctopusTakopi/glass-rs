/-
Shared vocabulary for the glass-rs model.

Machine integers are modelled as `Nat` plus explicit range facts, and every
Rust arithmetic operator the crate uses on `u64` gets its exact semantics
here: `saturating_add`/`saturating_mul` clamp at `U64_MAX`, and
`wrapping_add`/`wrapping_mul` reduce mod 2^64. Keeping these as plain `Nat`
functions (rather than `UInt64`) lets `omega`/`grind` do the arithmetic.
-/

namespace Glass

/-- `u64::MAX`. -/
def U64_MAX : Nat := 2 ^ 64 - 1

/-- `u32::MAX`: the null sentinel, and the pinned "infinity" key. -/
def U32_MAX : Nat := 2 ^ 32 - 1

/-- `MAX_SIZE`: trie capacity before preemption. -/
def MAX_SIZE : Nat := 4096

/-- Clamp an exact result into `u64`: what every saturating chain computes. -/
def sat (x : Nat) : Nat := min x U64_MAX

/-- `u64::saturating_add` on in-range operands. -/
def satAdd (a b : Nat) : Nat := sat (a + b)

/-- `u64::saturating_mul` on in-range operands. -/
def satMul (a b : Nat) : Nat := sat (a * b)

/-- `u64::wrapping_add`. -/
def wrapAdd (a b : Nat) : Nat := (a + b) % 2 ^ 64

/-- `u64::wrapping_mul`. -/
def wrapMul (a b : Nat) : Nat := (a * b) % 2 ^ 64

theorem U64_MAX_eq : U64_MAX = 18446744073709551615 := by decide
theorem U32_MAX_eq : U32_MAX = 4294967295 := by decide

theorem sat_le (x : Nat) : sat x ≤ U64_MAX := Nat.min_le_right _ _

theorem sat_of_le {x : Nat} (h : x ≤ U64_MAX) : sat x = x := Nat.min_eq_left h

theorem sat_mono {x y : Nat} (h : x ≤ y) : sat x ≤ sat y := by
  unfold sat; omega

/-- Saturating accumulation never loses information below the clamp:
adding a saturated term to a saturated running total is the saturation of
the exact sum. This is why a chain of `saturating_add(saturating_mul(..))`
equals `min(exact total, u64::MAX)`. -/
theorem satAdd_sat_sat (x y : Nat) : satAdd (sat x) (sat y) = sat (x + y) := by
  unfold satAdd sat; omega

theorem satAdd_sat (x y : Nat) : satAdd (sat x) y = sat (x + y) := by
  unfold satAdd sat; omega

theorem satMul_eq (a b : Nat) : satMul a b = sat (a * b) := rfl

theorem sat_sat (x : Nat) : sat (sat x) = sat x := by
  unfold sat; omega

theorem wrapAdd_of_lt {a b : Nat} (h : a + b < 2 ^ 64) : wrapAdd a b = a + b :=
  Nat.mod_eq_of_lt h

theorem wrapMul_of_lt {a b : Nat} (h : a * b < 2 ^ 64) : wrapMul a b = a * b :=
  Nat.mod_eq_of_lt h

end Glass
