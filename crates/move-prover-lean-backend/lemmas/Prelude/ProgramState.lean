import Prelude.UInt256
import Prelude.UInt128

-- Abort code type alias for clarity
abbrev AbortCode := Nat

-- Helper for abort in Except contexts
def abort {α : Type} (code : AbortCode) : Except AbortCode α :=
  Except.error code

-- ====================================================================================
-- HELPER LEMMAS FOR MOVE VERIFICATION
-- ====================================================================================
-- These lemmas provide infrastructure for proving properties of Move bytecode translations.
-- They are general-purpose and not specific to any particular Move program.

-- ------------------------------------------------------------------------------------
-- Section 1: Except Monad Simplification Lemmas
-- ------------------------------------------------------------------------------------
-- These lemmas enable simplification of monadic do-notation into normal form,
-- which is essential for reasoning about program execution.

namespace MoveExcept

-- Basic monad laws for pure and bind
@[simp] theorem pure_eq_ok {α : Type} (a : α) :
  (pure a : Except AbortCode α) = Except.ok a := rfl

@[simp] theorem bind_ok {α β : Type} (a : α) (f : α → Except AbortCode β) :
  (Except.ok a >>= f) = f a := rfl

@[simp] theorem bind_error {α β : Type} (n : AbortCode) (f : α → Except AbortCode β) :
  (Except.error n >>= f) = Except.error n := rfl

-- Left identity: pure a >>= f = f a
@[simp] theorem bind_pure_left {α β : Type} (a : α) (f : α → Except AbortCode β) :
  (pure a >>= f) = f a := rfl

-- Right identity: m >>= pure = m
@[simp] theorem bind_pure_right {α : Type} (m : Except AbortCode α) :
  (m >>= pure) = m := by
  cases m <;> rfl

-- Associativity: (m >>= f) >>= g = m >>= (fun x => f x >>= g)
@[simp] theorem bind_assoc {α β γ : Type} (m : Except AbortCode α) (f : α → Except AbortCode β) (g : β → Except AbortCode γ) :
  ((m >>= f) >>= g) = (m >>= fun x => f x >>= g) := by
  cases m <;> rfl

-- Simplification for nested pure binds
@[simp] theorem pure_bind_pure {α : Type} (a : α) :
  (pure a >>= pure : Except AbortCode α) = pure a := rfl

-- Simplification for do-notation patterns
@[simp] theorem do_ok {α β : Type} (a : α) (cont : α → Except AbortCode β) :
  (do let x := a; cont x) = cont a := rfl

-- Case analysis simplification
theorem ok_eq_iff {α : Type} (m : Except AbortCode α) (a : α) :
  m = Except.ok a ↔ ∃ b, m = Except.ok b ∧ b = a := by
  constructor
  · intro h; exact ⟨a, h, rfl⟩
  · intro ⟨b, hm, hb⟩; rw [hm, hb]

theorem error_eq_iff {α : Type} (m : Except AbortCode α) (n : AbortCode) :
  m = Except.error n ↔ ∃ k, m = Except.error k ∧ k = n := by
  constructor
  · intro h; exact ⟨n, h, rfl⟩
  · intro ⟨k, hm, hk⟩; rw [hm, hk]

end MoveExcept

-- While loop combinator for Except monad
-- Takes a condition function that receives current state,
-- a body function that receives and returns state,
-- and initial loop state
-- Returns the final loop state after the condition becomes false
-- NOTE: Marked partial until we can provide termination proofs
partial def whileLoop {α : Type}
  (cond : α → Except AbortCode Bool)
  (body : α → Except AbortCode α)
  (init : α) : Except AbortCode α := do
  let c ← cond init
  if c then
    let state' ← body init
    whileLoop cond body state'
  else
    pure init

-- Pure while loop combinator (for Id monad)
-- Used when the loop body has no aborts or monadic operations
-- NOTE: Marked partial until we can provide termination proofs
partial def whileLoopPure {α : Type}
  (cond : α → Id Bool)
  (body : α → Id α)
  (init : α) : Id α :=
  if Id.run (cond init) then
    whileLoopPure cond body (Id.run (body init))
  else
    pure init
