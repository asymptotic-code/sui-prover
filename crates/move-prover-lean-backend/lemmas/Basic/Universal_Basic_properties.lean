-- Lemmas for dependency functions
import Impls.Universal.Basic
import Prelude.UInt128
import Prelude.UInt256
import Prelude.Helpers
import Prelude.ProgramState

namespace Universal_Basic

-- bool_not_not
-- Category: basic
-- Generation: Manual
lemma bool_not_not (b : Bool) : ¬¬b = b := by
  cases b <;> rfl

-- bool_true_ne_false
-- Category: basic
-- Generation: Manual
lemma bool_true_ne_false : true ≠ false := by
  decide

-- option_some_ne_none
-- Category: basic
-- Generation: Manual
lemma option_some_ne_none {α : Type} (v : α) : some v ≠ none := by
  intro h; cases h

-- option_is_none_none
-- Category: basic
-- Generation: Manual
lemma option_is_none_none {α : Type} : (none : Option α).isNone = true := by
  rfl

-- option_is_some_some
-- Category: basic
-- Generation: Manual
lemma option_is_some_some {α : Type} (v : α) : (some v).isSome = true := by
  rfl

end Universal_Basic
