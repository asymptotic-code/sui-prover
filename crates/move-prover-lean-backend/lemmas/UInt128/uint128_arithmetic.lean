-- UInt128 Arithmetic Lemmas
-- These help with arithmetic operations and bounds reasoning

-- Addition commutativity
theorem uint128_add_comm (x y : UInt128) : x + y = y + x := by
  show UInt128.mk ((x.val + y.val) % UInt128.size) = UInt128.mk ((y.val + x.val) % UInt128.size)
  rw [Nat.add_comm]

-- Addition with zero
theorem uint128_add_zero (x : UInt128) : x + 0 = x := by
  show UInt128.mk ((x.val + 0) % UInt128.size) = x
  simp
  exact UInt128.val_injective rfl

theorem uint128_zero_add (x : UInt128) : 0 + x = x := by
  rw [uint128_add_comm]
  exact uint128_add_zero x

-- Bounds preservation for small values
theorem uint128_add_lt_of_lt {x y : UInt128} (hx : x.val < UInt128.size / 2) (hy : y.val < UInt128.size / 2) :
  (x + y).val < UInt128.size := by
  simp [HAdd.hAdd, Add.add, UInt128.add]
  have : x.val + y.val < UInt128.size := by omega
  simp [Nat.mod_eq_of_lt this]
  exact this

-- Comparison preserved under addition of same value
theorem uint128_lt_add_right {x y z : UInt128} (h : x < y) (hz : z.val + x.val < UInt128.size) (hz' : z.val + y.val < UInt128.size) :
  z.val + x.val < z.val + y.val := by
  show x.val < y.val at h
  omega

-- UInt128 maximum value
theorem uint128_max_val : (UInt128.size : Nat) = 340282366920938463463374607431768211456 := by
  rfl

-- Zero is minimum
theorem uint128_zero_min (x : UInt128) : 0 ≤ x := by
  show (0 : UInt128).val ≤ x.val
  simp
  exact Nat.zero_le _
