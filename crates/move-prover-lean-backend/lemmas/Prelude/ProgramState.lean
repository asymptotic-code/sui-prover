import Prelude.UInt256
import Prelude.UInt128

-- Program state for control flow
inductive ProgramState (α : Type) where
  | Returned : α -> ProgramState α
  | Aborted : Nat -> ProgramState α

def ProgramState.pure {α : Type} (a : α) : ProgramState α :=
  ProgramState.Returned a

def ProgramState.bind {α β : Type} (ma : ProgramState α) (f : α → ProgramState β) : ProgramState β :=
  match ma with
  | ProgramState.Returned a => f a
  | ProgramState.Aborted n => ProgramState.Aborted n

instance : Monad ProgramState where
  pure := ProgramState.pure
  bind := ProgramState.bind

-- Helper for abort in ProgramState contexts
def abort {α : Type} (code : Nat) : ProgramState α :=
  ProgramState.Aborted code

-- ====================================================================================
-- HELPER LEMMAS FOR MOVE VERIFICATION
-- ====================================================================================
-- These lemmas provide infrastructure for proving properties of Move bytecode translations.
-- They are general-purpose and not specific to any particular Move program.

-- ------------------------------------------------------------------------------------
-- Section 1: ProgramState Monad Simplification Lemmas
-- ------------------------------------------------------------------------------------
-- These lemmas enable simplification of monadic do-notation into normal form,
-- which is essential for reasoning about program execution.

namespace ProgramState

-- Basic monad laws for pure and bind
@[simp] theorem pure_eq_returned {α : Type} (a : α) :
  (pure a : ProgramState α) = ProgramState.Returned a := rfl

@[simp] theorem bind_returned {α β : Type} (a : α) (f : α → ProgramState β) :
  (ProgramState.Returned a >>= f) = f a := rfl

@[simp] theorem bind_aborted {α β : Type} (n : Nat) (f : α → ProgramState β) :
  (ProgramState.Aborted n >>= f) = ProgramState.Aborted n := rfl

-- Left identity: pure a >>= f = f a
@[simp] theorem bind_pure_left {α β : Type} (a : α) (f : α → ProgramState β) :
  (pure a >>= f) = f a := rfl

-- Right identity: m >>= pure = m
@[simp] theorem bind_pure_right {α : Type} (m : ProgramState α) :
  (m >>= pure) = m := by
  cases m <;> rfl

-- Associativity: (m >>= f) >>= g = m >>= (fun x => f x >>= g)
@[simp] theorem bind_assoc {α β γ : Type} (m : ProgramState α) (f : α → ProgramState β) (g : β → ProgramState γ) :
  ((m >>= f) >>= g) = (m >>= fun x => f x >>= g) := by
  cases m <;> rfl

-- Simplification for nested pure binds
@[simp] theorem pure_bind_pure {α : Type} (a : α) :
  (pure a >>= pure : ProgramState α) = pure a := rfl

-- Simplification for do-notation patterns
@[simp] theorem do_returned {α β : Type} (a : α) (cont : α → ProgramState β) :
  (do let x := a; cont x) = cont a := rfl

-- Case analysis simplification
theorem returned_eq_iff {α : Type} (m : ProgramState α) (a : α) :
  m = ProgramState.Returned a ↔ ∃ b, m = ProgramState.Returned b ∧ b = a := by
  constructor
  · intro h; exact ⟨a, h, rfl⟩
  · intro ⟨b, hm, hb⟩; rw [hm, hb]

theorem aborted_eq_iff {α : Type} (m : ProgramState α) (n : Nat) :
  m = ProgramState.Aborted n ↔ ∃ k, m = ProgramState.Aborted k ∧ k = n := by
  constructor
  · intro h; exact ⟨n, h, rfl⟩
  · intro ⟨k, hm, hk⟩; rw [hm, hk]

end ProgramState

-- While loop combinator for ProgramState monad
-- Takes a condition function, body function, and initial loop state
-- Returns the final loop state after the condition becomes false
partial def whileLoop {α : Type}
  (cond : Unit → ProgramState Bool)
  (body : Unit → ProgramState α)
  (init : α) : ProgramState α := do
  let c ← cond ()
  if c then
    let state' ← body ()
    whileLoop cond body state'
  else
    pure init
