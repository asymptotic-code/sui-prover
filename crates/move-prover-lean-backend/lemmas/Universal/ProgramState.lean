import Lemmas.Universal.UInt256
import Lemmas.Universal.UInt128
import Lemmas.Universal.ToNatHelper

-- Program state for control flow
-- NOTE: AtBlock removed - only Returned and Aborted are needed
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

def prover_requires (cond : Bool) : ProgramState Unit :=
  if cond then
    pure ()
  else
    ProgramState.Aborted 0

def prover_ensures (cond : Bool) : ProgramState Unit :=
  if cond then
    pure ()
  else
    ProgramState.Aborted 0

-- Helper for abort in StateT contexts
def abortStateT {s α : Type} (code : Nat) : StateT s ProgramState α :=
  fun _ => ProgramState.Aborted code

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

-- ------------------------------------------------------------------------------------
-- Section 2: StateT Reasoning Lemmas - REMOVED
-- ------------------------------------------------------------------------------------
-- NOTE: StateT reasoning lemmas were removed to avoid conflicts with Lean 4's
-- standard library. Use the standard library's StateT lemmas instead.

-- ------------------------------------------------------------------------------------
-- Section 3: runVerified Combinator
-- ------------------------------------------------------------------------------------
-- The runVerified combinator extracts a value from a ProgramState computation when we
-- have proof that it returns successfully. This enables zero-duplication pure functions
-- by allowing them to call runtime functions and extract the result.

/-- Extract the returned value from a ProgramState when we know it returns successfully. -/
def runVerified {α : Type}
  (computation : ProgramState α)
  (h : ∃ result, computation = ProgramState.Returned result)
  : α :=
  match computation with
  | ProgramState.Returned result => result
  | ProgramState.Aborted code =>
      False.elim (by
        obtain ⟨r, hr⟩ := h
        cases hr
      )

/-- Key lemma: runVerified preserves the Returned value. -/
theorem runVerified_eq {α : Type}
  (computation : ProgramState α)
  (h : ∃ result, computation = ProgramState.Returned result)
  : computation = ProgramState.Returned (runVerified computation h) := by
  obtain ⟨result, hr⟩ := h
  cases hr
  rfl

-- ====================================================================================
-- END HELPER LEMMAS
-- ====================================================================================

-- Lift Except String into ProgramState
-- Treats errors as aborts with code 0
def liftExceptToProgramState {α : Type} (e : Except String α) : ProgramState α :=
  match e with
  | Except.ok a => ProgramState.Returned a
  | Except.error _ => ProgramState.Aborted 0

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
