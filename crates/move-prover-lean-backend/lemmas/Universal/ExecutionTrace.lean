-- ExecutionTrace for Spec Functions
-- ExecutionTrace represents the result of executing a spec function, including:
-- - The returned value (if successful)
-- - A list of requires clause evaluations (stored as List Bool)
-- - A list of ensures clause evaluations (stored as List Bool)
-- - Abort information (if the function aborted)

import Lemmas.Universal.ProgramState

inductive ExecutionTrace (α : Type) where
  | Aborted : Nat → ExecutionTrace α
  | Returned : α → List Bool → List Bool → ExecutionTrace α
  deriving Repr

namespace ExecutionTrace

def isReturned {α : Type} : ExecutionTrace α → Bool
  | Returned _ _ _ => true
  | _ => false

def isAborted {α : Type} : ExecutionTrace α → Bool
  | Aborted _ => true
  | _ => false

def getResult! {α : Type} [Inhabited α] : ExecutionTrace α → α
  | Returned r _ _ => r
  | Aborted n => panic! s!"ExecutionTrace.Aborted {n}"

def getRequires! {α : Type} : ExecutionTrace α → List Bool
  | Returned _ reqs _ => reqs
  | Aborted _ => []

def getEnsures! {α : Type} : ExecutionTrace α → List Bool
  | Returned _ _ ens => ens
  | Aborted _ => []

-- Helper: check if specific requires index is true
def requireAt? {α : Type} (idx : Nat) : ExecutionTrace α → Option Bool
  | Returned _ reqs _ => reqs[idx]?
  | _ => none

-- Helper: check if specific ensures index is true
def ensureAt? {α : Type} (idx : Nat) : ExecutionTrace α → Option Bool
  | Returned _ _ ens => ens[idx]?
  | _ => none

-- Helper: get abort code if aborted
def getAbortCode? {α : Type} : ExecutionTrace α → Option Nat
  | Aborted code => some code
  | _ => none

-- Monad instance for ExecutionTrace
instance : Monad ExecutionTrace where
  pure a := ExecutionTrace.Returned a [] []
  bind m f := match m with
    | ExecutionTrace.Aborted code => ExecutionTrace.Aborted code
    | ExecutionTrace.Returned val _ _ => f val

-- Monad simplification lemmas
@[simp] theorem pure_eq_returned {α : Type} (a : α) :
  (pure a : ExecutionTrace α) = ExecutionTrace.Returned a [] [] := rfl

@[simp] theorem bind_returned {α β : Type} (a : α) (reqs : List Bool) (ens : List Bool) (f : α → ExecutionTrace β) :
  (ExecutionTrace.Returned a reqs ens >>= f) = f a := rfl

@[simp] theorem bind_aborted {α β : Type} (n : Nat) (f : α → ExecutionTrace β) :
  (ExecutionTrace.Aborted n >>= f) = ExecutionTrace.Aborted n := rfl

@[simp] theorem bind_pure_left {α β : Type} (a : α) (f : α → ExecutionTrace β) :
  (pure a >>= f) = f a := rfl

@[simp] theorem bind_pure_right {α : Type} (m : ExecutionTrace α) :
  (m >>= pure) = match m with
    | ExecutionTrace.Aborted n => ExecutionTrace.Aborted n
    | ExecutionTrace.Returned v _ _ => ExecutionTrace.Returned v [] []
    := by cases m <;> rfl

end ExecutionTrace

-- Conversion from ProgramState to ExecutionTrace
def liftProgramState {α : Type} (ps : ProgramState α) : ExecutionTrace α :=
  match ps with
  | ProgramState.Returned val => ExecutionTrace.Returned val [] []
  | ProgramState.Aborted code => ExecutionTrace.Aborted code

-- Simplification for liftProgramState
@[simp] theorem liftProgramState_returned {α : Type} (a : α) :
  liftProgramState (ProgramState.Returned a) = ExecutionTrace.Returned a [] [] := rfl

@[simp] theorem liftProgramState_aborted {α : Type} (n : Nat) :
  liftProgramState (ProgramState.Aborted n : ProgramState α) = ExecutionTrace.Aborted n := rfl

-- Helper: lift a ProgramState computation into ExecutionTrace monad
instance {α : Type} : Coe (ProgramState α) (ExecutionTrace α) where
  coe := liftProgramState
