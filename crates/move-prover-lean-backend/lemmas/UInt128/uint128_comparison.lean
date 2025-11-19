-- UInt128 Comparison Lemmas
-- Proven lemmas for reasoning about UInt128 comparisons
import Prelude.UInt128

-- Reflexivity lemmas
theorem uint128_le_refl (x : UInt128) : x ≤ x := by
  show x.val ≤ x.val
  exact Nat.le_refl _

theorem uint128_lt_irrefl (x : UInt128) : ¬(x < x) := by
  show ¬(x.val < x.val)
  exact Nat.lt_irrefl _

-- Transitivity lemmas
theorem uint128_le_trans {x y z : UInt128} : x ≤ y → y ≤ z → x ≤ z := by
  intro hxy hyz
  show x.val ≤ z.val
  exact Nat.le_trans hxy hyz

theorem uint128_lt_trans {x y z : UInt128} : x < y → y < z → x < z := by
  intro hxy hyz
  show x.val < z.val
  exact Nat.lt_trans hxy hyz

-- Mixed transitivity
theorem uint128_lt_le_trans {x y z : UInt128} : x < y → y ≤ z → x < z := by
  intro hxy hyz
  show x.val < z.val
  exact Nat.lt_of_lt_of_le hxy hyz

theorem uint128_le_lt_trans {x y z : UInt128} : x ≤ y → y < z → x < z := by
  intro hxy hyz
  show x.val < z.val
  exact Nat.lt_of_le_of_lt hxy hyz

-- Conversion lemmas
theorem uint128_lt_to_le {x y : UInt128} : x < y → x ≤ y := by
  intro h
  show x.val ≤ y.val
  exact Nat.le_of_lt h

theorem uint128_not_lt_to_ge {x y : UInt128} : ¬(x < y) → y ≤ x := by
  intro h
  show y.val ≤ x.val
  exact Nat.ge_of_not_lt h

theorem uint128_not_le_to_gt {x y : UInt128} : ¬(x ≤ y) → y < x := by
  intro h
  show y.val < x.val
  exact Nat.not_le.mp h

-- Decidability simplification
theorem uint128_decide_le_true {x y : UInt128} : x ≤ y → decide (x ≤ y) = true := by
  intro h
  simp [h]

theorem uint128_decide_lt_true {x y : UInt128} : x < y → decide (x < y) = true := by
  intro h
  simp [h]

theorem uint128_decide_le_false {x y : UInt128} : ¬(x ≤ y) → decide (x ≤ y) = false := by
  intro h
  simp [h]

theorem uint128_decide_lt_false {x y : UInt128} : ¬(x < y) → decide (x < y) = false := by
  intro h
  simp [h]

-- Bounds lemmas
theorem uint128_zero_le (x : UInt128) : (0 : UInt128) ≤ x := by
  show (0 : UInt128).val ≤ x.val
  exact Nat.zero_le _

theorem uint128_lt_size {x : UInt128} : x.toNat < UInt128.size := by
  exact x.val.isLt
