-- ProgramState Lemmas
-- These help with lifting values and monadic reasoning

-- Basic lifting lemmas
theorem liftProgramState_pure {α : Type} (x : α) :
  liftProgramState (pure x : ProgramState α) = pure x := by
  simp [liftProgramState]
  rfl

theorem liftProgramState_returned {α : Type} (x : α) :
  liftProgramState (ProgramState.Returned x) = pure x := by
  simp [liftProgramState]
  rfl

-- Lemma: lifting an aborted state propagates the abort
theorem liftProgramState_aborted {α β : Type} (n : Nat) :
  (liftProgramState (ProgramState.Aborted n : ProgramState α) : ExecutionTrace β) = ExecutionTrace.Aborted n := by
  simp [liftProgramState]
  rfl

-- Lemma: if liftProgramState succeeds, the inner ProgramState succeeded
theorem liftProgramState_eq_pure_iff {α : Type} (ps : ProgramState α) (x : α) :
  liftProgramState ps = pure x ↔ ps = ProgramState.Returned x := by
  simp [liftProgramState]
  cases ps <;> simp

-- Lemma: liftProgramState preserves equality
theorem liftProgramState_eq {α : Type} (ps1 ps2 : ProgramState α) (h : ps1 = ps2) :
  liftProgramState ps1 = liftProgramState ps2 := by
  rw [h]
