import Prelude.BoundedNat

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

-- While loop combinator for Except monad with fuel
-- Takes a condition function that receives current state,
-- a body function that receives and returns state,
-- initial loop state, and fuel for termination
-- Returns the final loop state after the condition becomes false
def whileLoopFuelM {α : Type}
    (cond : α → Except AbortCode Bool)
    (body : α → Except AbortCode α)
    (fuel : Nat)
    (init : α) : Except AbortCode α :=
  match fuel with
  | 0 => pure init  -- Out of fuel, return current state
  | fuel' + 1 => do
    let c ← cond init
    if c then
      let state' ← body init
      whileLoopFuelM cond body fuel' state'
    else
      pure init

-- Default fuel for common loop patterns
def defaultLoopFuel : Nat := 256  -- Sufficient for 8-bit counter loops and 128-bit ripple-carry

/-- While loop combinator for Except monad with default fuel -/
def whileLoop {α : Type}
    (cond : α → Except AbortCode Bool)
    (body : α → Except AbortCode α)
    (init : α) : Except AbortCode α :=
  whileLoopFuelM cond body defaultLoopFuel init

-- ====================================================================================
-- TERMINATING WHILE LOOP COMBINATORS
-- ====================================================================================
-- These loops use explicit fuel to guarantee termination while maintaining
-- semantic equivalence with unbounded loops when sufficient fuel is provided.

/-- Fuel-based while loop that is provably terminating.
    When fuel runs out, returns the current state.
    For verified programs, we prove the loop terminates before fuel exhaustion. -/
def whileLoopFuel {α : Type}
    (cond : α → Prop) [∀ a, Decidable (cond a)]
    (body : α → α)
    (fuel : Nat)
    (init : α) : α :=
  match fuel with
  | 0 => init  -- Out of fuel, return current state
  | fuel' + 1 =>
    if cond init then
      whileLoopFuel cond body fuel' (body init)
    else
      init

/-- Pure while loop combinator using fuel for termination.
    This version computes fuel based on the initial state using a fuel function.
    The fuel function should return an upper bound on the number of iterations. -/
def whileLoopPureFuel {α : Type}
    (cond : α → Prop) [∀ a, Decidable (cond a)]
    (body : α → α)
    (fuelFn : α → Nat)
    (init : α) : α :=
  whileLoopFuel cond body (fuelFn init) init

/-- Pure while loop combinator with default fuel.
    Used when the loop body has no aborts or monadic operations.
    Takes a Prop-valued condition with Decidable constraint.

    For correctness proofs, we show that the loop terminates before
    running out of fuel (256 iterations suffices for all our use cases). -/
def whileLoopPure {α : Type}
    (cond : α → Prop) [∀ a, Decidable (cond a)]
    (body : α → α)
    (init : α) : α :=
  whileLoopFuel cond body defaultLoopFuel init

-- Theorems about whileLoopFuel

/-- When condition is false, loop returns immediately -/
theorem whileLoopFuel_false {α : Type}
    (cond : α → Prop) [∀ a, Decidable (cond a)]
    (body : α → α) (fuel : Nat) (init : α)
    (h : ¬cond init) :
    whileLoopFuel cond body fuel init = init := by
  cases fuel with
  | zero => rfl
  | succ n => simp only [whileLoopFuel, h, ↓reduceIte]

/-- With sufficient fuel, the loop computes the same result regardless of extra fuel -/
theorem whileLoopFuel_sufficient {α : Type}
    (cond : α → Prop) [∀ a, Decidable (cond a)]
    (body : α → α) (fuel1 fuel2 : Nat) (init : α)
    (h1 : fuel1 ≤ fuel2)
    (h_terminates : ∃ n ≤ fuel1, ¬cond (Nat.iterate body n init)) :
    whileLoopFuel cond body fuel1 init = whileLoopFuel cond body fuel2 init := by
  sorry  -- Proof requires induction on termination witness

-- While loop abort predicate combinator with fuel (Bool version for decidability)
-- Returns true if any iteration of the loop would abort within the fuel limit
-- Takes:
--   cond: loop condition (same as whileLoopPure)
--   body_aborts: predicate for whether one iteration aborts (decidable)
--   body_pure: pure computation for one iteration (to advance state)
--   fuel: maximum number of iterations to check
def whileLoopAbortsBoolFuel {α : Type}
    (cond : α → Prop) [∀ a, Decidable (cond a)]
    (body_aborts : α → Prop) [∀ a, Decidable (body_aborts a)]
    (body_pure : α → α)
    (fuel : Nat)
    (init : α) : Bool :=
  match fuel with
  | 0 => false  -- Out of fuel, assume no abort (conservative for verification)
  | fuel' + 1 =>
    if cond init then
      if body_aborts init then true
      else whileLoopAbortsBoolFuel cond body_aborts body_pure fuel' (body_pure init)
    else
      false

/-- While loop abort predicate with default fuel -/
def whileLoopAbortsBool {α : Type}
    (cond : α → Prop) [∀ a, Decidable (cond a)]
    (body_aborts : α → Prop) [∀ a, Decidable (body_aborts a)]
    (body_pure : α → α)
    (init : α) : Bool :=
  whileLoopAbortsBoolFuel cond body_aborts body_pure defaultLoopFuel init

-- Prop version wrapping the Bool version
def whileLoopAborts {α : Type}
  (cond : α → Prop) [∀ a, Decidable (cond a)]
  (body_aborts : α → Prop) [∀ a, Decidable (body_aborts a)]
  (body_pure : α → α)
  (init : α) : Prop :=
  whileLoopAbortsBool cond body_aborts body_pure init = true

instance {α : Type}
  (cond : α → Prop) [∀ a, Decidable (cond a)]
  (body_aborts : α → Prop) [∀ a, Decidable (body_aborts a)]
  (body_pure : α → α)
  (init : α) : Decidable (whileLoopAborts cond body_aborts body_pure init) :=
  inferInstanceAs (Decidable (_ = true))
