/-
# BoundedNat Theorems

Proves that BoundedNat operations have the expected mathematical properties.
-/

import Prelude.BoundedNat

namespace BoundedNat

open BoundedNat

variable {bound : Nat}

/-- Shift right equals floor division by power of 2 (Nat version) -/
theorem shiftRight_eq_div (a : BoundedNat bound) (k : Nat) :
  (shiftRight a k).val = a.val / 2^k := by
  unfold shiftRight
  simp only [Nat.shiftRight_eq_div_pow]

/-- mul_shr operation (multiply then shift right) -/
def mul_shr {bound1 bound2 : Nat} (a : BoundedNat bound1) (b : BoundedNat bound2) (shift : Nat) : Nat :=
  (a.val * b.val) >>> shift

/-- mul_shr equals division -/
theorem mul_shr_eq_div {bound1 bound2 : Nat} (a : BoundedNat bound1) (b : BoundedNat bound2) (shift : Nat) :
  mul_shr a b shift = (a.val * b.val) / 2^shift := by
  unfold mul_shr
  rw [Nat.shiftRight_eq_div_pow]

/-- Shift right is bounded -/
theorem shiftRight_bounded (a : BoundedNat bound) (k : Nat) :
  (shiftRight a k).val < bound := by
  unfold shiftRight
  have : a.val >>> k ≤ a.val := Nat.shiftRight_le a.val k
  exact Nat.lt_of_le_of_lt this a.property

end BoundedNat
