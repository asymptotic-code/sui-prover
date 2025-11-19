-- ProgramState Lifting Lemmas
-- Lemmas for reasoning about lifting values and operations into ProgramState
import Prelude.ProgramState
import Prelude.UInt128
import Prelude.ExecutionTrace

namespace ProgramStateLemmas

-- Basic lifting lemmas
lemma returned_not_aborted {α : Type} (a : α) (n : Nat) :
    ProgramState.Returned a ≠ ProgramState.Aborted n := by
  intro h
  cases h

lemma aborted_not_returned {α : Type} (a : α) (n : Nat) :
    ProgramState.Aborted n ≠ ProgramState.Returned a := by
  intro h
  cases h

-- Bind preserves Returned
lemma bind_returned_returned {α β : Type} (a : α) (f : α → ProgramState β) (b : β) :
    f a = ProgramState.Returned b → (ProgramState.Returned a >>= f) = ProgramState.Returned b := by
  intro h
  simp [h]

-- Bind preserves Aborted
lemma bind_returned_aborted {α β : Type} (a : α) (f : α → ProgramState β) (n : Nat) :
    f a = ProgramState.Aborted n → (ProgramState.Returned a >>= f) = ProgramState.Aborted n := by
  intro h
  simp [h]

-- Monotonicity: if property holds for inner value, it holds after bind
lemma bind_preserves_property {α β : Type} (P : β → Prop) (m : ProgramState α) (f : α → ProgramState β) :
    (∀ a, m = ProgramState.Returned a → ∃ b, f a = ProgramState.Returned b ∧ P b) →
    (∃ b, (m >>= f) = ProgramState.Returned b ∧ P b) ∨ (∃ n, (m >>= f) = ProgramState.Aborted n) := by
  intro h
  cases m
  case Returned a =>
    obtain ⟨b, hf, hP⟩ := h a rfl
    left
    exists b
    simp [hf, hP]
  case Aborted n =>
    right
    exists n
    simp

-- If computation returns, we can extract the value
lemma returned_exists_value {α : Type} (m : ProgramState α) :
    (∃ a, m = ProgramState.Returned a) ∨ (∃ n, m = ProgramState.Aborted n) := by
  cases m
  case Returned a => left; exists a
  case Aborted n => right; exists n

-- Pure computation lemmas
lemma pure_is_returned {α : Type} (a : α) :
    ProgramState.pure a = ProgramState.Returned a := by
  rfl

lemma pure_not_aborted {α : Type} (a : α) (n : Nat) :
    ProgramState.pure a ≠ ProgramState.Aborted n := by
  intro h
  cases h

-- Do-notation simplification
lemma do_pure_bind {α β : Type} (a : α) (f : α → ProgramState β) :
    (do let x ← ProgramState.pure a; f x) = f a := by
  simp

lemma do_bind_pure {α : Type} (m : ProgramState α) :
    (do let x ← m; ProgramState.pure x) = m := by
  cases m <;> simp

end ProgramStateLemmas

-- ExecutionTrace to ProgramState lifting
namespace ExecutionTraceLemmas

-- liftProgramState properties
def liftProgramState {α : Type} (ps : ProgramState α) : ExecutionTrace α :=
  match ps with
  | ProgramState.Returned a => ExecutionTrace.Returned a [] []
  | ProgramState.Aborted n => ExecutionTrace.Aborted n

lemma liftProgramState_returned {α : Type} (a : α) :
    liftProgramState (ProgramState.Returned a) = ExecutionTrace.Returned a [] [] := by
  rfl

lemma liftProgramState_aborted {α : Type} (n : Nat) :
    liftProgramState (ProgramState.Aborted n) = ExecutionTrace.Aborted n := by
  rfl

-- Bind preservation for liftProgramState
lemma liftProgramState_bind {α β : Type} (m : ProgramState α) (f : α → ProgramState β) :
    liftProgramState (m >>= f) =
      match liftProgramState m with
      | ExecutionTrace.Returned a _ _ => liftProgramState (f a)
      | ExecutionTrace.Aborted n => ExecutionTrace.Aborted n := by
  cases m <;> simp [liftProgramState, ProgramState.bind]

-- Pure preservation
lemma liftProgramState_pure {α : Type} (a : α) :
    liftProgramState (ProgramState.pure a) = ExecutionTrace.Returned a [] [] := by
  rfl

end ExecutionTraceLemmas
