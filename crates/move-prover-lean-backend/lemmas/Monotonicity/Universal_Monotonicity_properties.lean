-- Lemmas for dependency functions
import Impls.Universal.Monotonicity
import Prelude.UInt128
import Prelude.UInt256
import Prelude.Helpers
import Prelude.ProgramState

namespace Universal_Monotonicity

-- nat_add_lt_add_left
-- Category: monotonicity
-- Generation: Manual
lemma nat_add_lt_add_left {a b : Nat} (c : Nat) : a < b → c + a < c + b := by
  omega

-- nat_mul_lt_mul_left
-- Category: monotonicity
-- Generation: Manual
lemma nat_mul_lt_mul_left {a b : Nat} (c : Nat) (hc : 0 < c) : a < b → c * a < c * b := by
  omega

-- nat_add_lt_add_right
-- Category: monotonicity
-- Generation: Manual
lemma nat_add_lt_add_right {a b : Nat} (c : Nat) : a < b → a + c < b + c := by
  omega

end Universal_Monotonicity
