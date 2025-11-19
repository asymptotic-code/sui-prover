-- Lemmas for dependency functions
import Impls.Universal.Arithmetic
import Prelude.UInt128
import Prelude.UInt256
import Prelude.Helpers
import Prelude.ProgramState

namespace Universal_Arithmetic

-- nat_add_assoc
-- Category: arithmetic
-- Generation: Manual
lemma nat_add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  omega

-- nat_lt_trans
-- Category: arithmetic
-- Generation: Manual
lemma nat_lt_trans {a b c : Nat} : a < b → b < c → a < c := by
  omega

-- nat_add_zero
-- Category: arithmetic
-- Generation: Manual
lemma nat_add_zero (n : Nat) : n + 0 = n := by
  omega

-- nat_le_refl
-- Category: arithmetic
-- Generation: Manual
lemma nat_le_refl (n : Nat) : n ≤ n := by
  omega

-- nat_zero_add
-- Category: arithmetic
-- Generation: Manual
lemma nat_zero_add (n : Nat) : 0 + n = n := by
  rfl

-- nat_lt_irrefl
-- Category: arithmetic
-- Generation: Manual
lemma nat_lt_irrefl (n : Nat) : ¬(n < n) := by
  omega

-- nat_mul_comm
-- Category: arithmetic
-- Generation: Manual
lemma nat_mul_comm (a b : Nat) : a * b = b * a := by
  omega

-- nat_add_comm
-- Category: arithmetic
-- Generation: Manual
lemma nat_add_comm (a b : Nat) : a + b = b + a := by
  omega

end Universal_Arithmetic
