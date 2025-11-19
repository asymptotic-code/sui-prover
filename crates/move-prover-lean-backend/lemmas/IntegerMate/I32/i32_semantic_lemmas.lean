-- Semantic lemmas for I32 signed integer operations
-- These lemmas capture the mathematical properties needed to reason about I32 comparison and arithmetic

import Impls.IntegerMate.I32
import Prelude.UInt128
import Prelude.UInt256
import Prelude.Helpers
import Prelude.ProgramState

namespace IntegerMate_I32

-- ============================================================================
-- Comparison Function (cmp) Properties
-- ============================================================================

-- cmp returns 0, 1, or 2
axiom cmp_range (num1 num2 : I32) :
  ∀ (result : UInt8), cmp num1 num2 = ProgramState.Returned result →
  result = 0 ∨ result = 1 ∨ result = 2

-- cmp is reflexive: x cmp x = 1 (equal)
axiom cmp_refl (x : I32) :
  cmp x x = ProgramState.Returned 1

-- cmp is antisymmetric: if x < y then y > x
axiom cmp_antisym (x y : I32) :
  ∀ (rx ry : UInt8),
  cmp x y = ProgramState.Returned rx →
  cmp y x = ProgramState.Returned ry →
  (rx = 0 → ry = 2) ∧ (rx = 2 → ry = 0) ∧ (rx = 1 → ry = 1)

-- cmp is transitive
axiom cmp_trans_lt (x y z : I32) :
  cmp x y = ProgramState.Returned 0 →
  cmp y z = ProgramState.Returned 0 →
  cmp x z = ProgramState.Returned 0

axiom cmp_trans_gt (x y z : I32) :
  cmp x y = ProgramState.Returned 2 →
  cmp y z = ProgramState.Returned 2 →
  cmp x z = ProgramState.Returned 2

-- ============================================================================
-- Comparison Operator Properties
-- ============================================================================

-- lt is consistent with cmp
axiom lt_iff_cmp_zero (x y : I32) :
  ∀ (b : Bool) (c : UInt8),
  lt x y = ProgramState.Returned b →
  cmp x y = ProgramState.Returned c →
  b = true ↔ c = 0

-- lte is consistent with cmp
axiom lte_iff_cmp_le_one (x y : I32) :
  ∀ (b : Bool) (c : UInt8),
  lte x y = ProgramState.Returned b →
  cmp x y = ProgramState.Returned c →
  b = true ↔ (c = 0 ∨ c = 1)

-- gte is consistent with cmp
axiom gte_iff_cmp_ge_one (x y : I32) :
  ∀ (b : Bool) (c : UInt8),
  gte x y = ProgramState.Returned b →
  cmp x y = ProgramState.Returned c →
  b = true ↔ (c = 1 ∨ c = 2)

-- ============================================================================
-- Monotonicity Properties
-- ============================================================================

-- If x < y and y < z, then x < z
axiom lt_trans (x y z : I32) :
  ∀ (bxy byz : Bool),
  lt x y = ProgramState.Returned bxy →
  lt y z = ProgramState.Returned byz →
  bxy = true → byz = true →
  ∃ (bxz : Bool), lt x z = ProgramState.Returned bxz ∧ bxz = true

-- If x ≤ y and y ≤ z, then x ≤ z
axiom lte_trans (x y z : I32) :
  ∀ (bxy byz : Bool),
  lte x y = ProgramState.Returned bxy →
  lte y z = ProgramState.Returned byz →
  bxy = true → byz = true →
  ∃ (bxz : Bool), lte x z = ProgramState.Returned bxz ∧ bxz = true

-- ============================================================================
-- Bounds and Validity Properties
-- ============================================================================

-- from succeeds for values ≤ MAX_POSITIVE (2^31 - 1)
axiom from_valid_range (v : UInt32) :
  v ≤ 2147483647 →
  ∃ (i : I32), «from» v = ProgramState.Returned i

-- from aborts for values > MAX_POSITIVE
axiom from_out_of_range (v : UInt32) :
  v > 2147483647 →
  ∃ (code : Nat), «from» v = ProgramState.Aborted code

-- neg_from succeeds for values ≤ MIN_NEGATIVE_ABS (2^31)
axiom neg_from_valid_range (v : UInt32) :
  v ≤ 2147483648 →
  ∃ (i : I32), neg_from v = ProgramState.Returned i

-- neg_from aborts for values > MIN_NEGATIVE_ABS
axiom neg_from_out_of_range (v : UInt32) :
  v > 2147483648 →
  ∃ (code : Nat), neg_from v = ProgramState.Aborted code

-- ============================================================================
-- Sign Properties
-- ============================================================================

-- sign returns 0 or 1
axiom sign_range (v : I32) :
  ∀ (s : UInt8), sign v = ProgramState.Returned s →
  s = 0 ∨ s = 1

-- Negative numbers have sign bit 1
axiom is_neg_iff_sign_one (v : I32) :
  ∀ (b : Bool) (s : UInt8),
  is_neg v = ProgramState.Returned b →
  sign v = ProgramState.Returned s →
  b = true ↔ s = 1

-- Positive numbers (from valid range) have sign bit 0
axiom from_has_sign_zero (v : UInt32) (i : I32) :
  v ≤ 2147483647 →
  «from» v = ProgramState.Returned i →
  ∃ (s : UInt8), sign i = ProgramState.Returned s ∧ s = 0

-- Negative numbers (from neg_from, v > 0) have sign bit 1
axiom neg_from_has_sign_one (v : UInt32) (i : I32) :
  0 < v → v ≤ 2147483648 →
  neg_from v = ProgramState.Returned i →
  ∃ (s : UInt8), sign i = ProgramState.Returned s ∧ s = 1

-- ============================================================================
-- Arithmetic Properties
-- ============================================================================

-- Addition commutativity (when both succeed)
axiom add_comm (x y : I32) :
  ∀ (rxy ryx : I32),
  add x y = ProgramState.Returned rxy →
  add y x = ProgramState.Returned ryx →
  rxy = ryx

-- Subtraction anti-commutativity (when both succeed)
axiom sub_antisym (x y : I32) :
  ∀ (rxy ryx : I32),
  sub x y = ProgramState.Returned rxy →
  sub y x = ProgramState.Returned ryx →
  ∃ (neg_rxy : I32), wrapping_sub (I32.mk 0) rxy = ProgramState.Returned neg_rxy ∧ neg_rxy = ryx

-- abs of positive number is identity
axiom abs_of_positive (v : I32) :
  ∀ (s : UInt8) (av : I32),
  sign v = ProgramState.Returned s →
  s = 0 →
  abs v = ProgramState.Returned av →
  av = v

end IntegerMate_I32
