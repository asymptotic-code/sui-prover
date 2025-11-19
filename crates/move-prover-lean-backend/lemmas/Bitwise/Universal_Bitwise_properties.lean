-- Lemmas for dependency functions
import Impls.Universal.Bitwise
import Prelude.UInt128
import Prelude.UInt256
import Prelude.Helpers
import Prelude.ProgramState

namespace Universal_Bitwise

-- uint_or_comm
-- Category: bitwise
-- Generation: Manual
lemma uint_or_comm {n : Nat} (a b : Fin (2^n)) : (a ||| b) = (b ||| a) := by
  ext; simp [HOr.hOr, OrOp.or]; omega

-- uint_and_comm
-- Category: bitwise
-- Generation: Manual
lemma uint_and_comm {n : Nat} (a b : Fin (2^n)) : (a &&& b) = (b &&& a) := by
  ext; simp [HAnd.hAnd, AndOp.and]; omega

end Universal_Bitwise
