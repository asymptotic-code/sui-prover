-- Lemmas for dependency functions
import Impls.Universal.ProgramState
import Prelude.UInt128
import Prelude.UInt256
import Prelude.Helpers
import Prelude.ProgramState

namespace Universal_ProgramState

-- program_state_bind_aborted
-- Category: program_state
-- Generation: Manual
lemma program_state_bind_aborted {α β : Type} (n : Nat) (f : α → ProgramState β) : (ProgramState.Aborted n >>= f) = ProgramState.Aborted n := by
  rfl

-- program_state_bind_returned
-- Category: program_state
-- Generation: Manual
lemma program_state_bind_returned {α β : Type} (v : α) (f : α → ProgramState β) : (ProgramState.Returned v >>= f) = f v := by
  rfl

-- program_state_returned_ne_aborted
-- Category: program_state
-- Generation: Manual
lemma program_state_returned_ne_aborted {α : Type} (v : α) (n : Nat) : ProgramState.Returned v ≠ ProgramState.Aborted n := by
  intro h; cases h

end Universal_ProgramState
