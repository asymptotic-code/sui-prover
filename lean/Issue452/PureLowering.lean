import Issue452.Core

namespace Issue452

/-!
# PureLowering

This file isolates the constructor-only lowering story:

- define a tiny source-expression language with constructor forms only
- evaluate the source form
- lower it into the target enum directly
- prove that the lowering preserves both the witness predicate and the top-level property
-/

inductive SourceExpr where
  | ctorA
  | ctorB (v : Nat)
deriving DecidableEq, Repr

/-! ## Constructor-only source language -/

def evalSource : SourceExpr → E
  | .ctorA => .A
  | .ctorB v => .B v

def lowerSource : SourceExpr → E
  | .ctorA => lowerPackVariantA
  | .ctorB v => lowerPackVariantB v

theorem lowerSource_sound (expr : SourceExpr) : lowerSource expr = evalSource expr := by
  cases expr with
  | ctorA =>
      simp [lowerSource, evalSource, lowerPackVariantA]
  | ctorB v =>
      simp [lowerSource, evalSource, lowerPackVariantB]

def evalIsBSource (target : Nat) : SourceExpr → Prop
  | .ctorA => False
  | .ctorB v => v = target

def evalIsBLowered (target : Nat) (expr : SourceExpr) : Prop :=
  isB target (lowerSource expr)

theorem evalIsB_preserved (target : Nat) (expr : SourceExpr) :
    evalIsBLowered target expr ↔ evalIsBSource target expr := by
  cases expr with
  | ctorA =>
      simp [evalIsBLowered, evalIsBSource, lowerSource, lowerPackVariantA, isB]
  | ctorB v =>
      simp [evalIsBLowered, evalIsBSource, lowerSource, lowerPackVariantB, isB]

def evalF2Source : SourceExpr → Prop :=
  f2 ∘ evalSource

def evalF2Lowered : SourceExpr → Prop :=
  f2 ∘ lowerSource

theorem evalF2_preserved (expr : SourceExpr) :
    evalF2Lowered expr ↔ evalF2Source expr := by
  simp [evalF2Lowered, evalF2Source, lowerSource_sound]

theorem ctorB_has_witness_after_lowering (v : Nat) :
    ∃ witness, isB witness (lowerSource (.ctorB v)) := by
  refine ⟨v, ?_⟩
  simp [lowerSource, lowerPackVariantB, isB]

theorem lowering_preserves_totality (expr : SourceExpr) : evalF2Lowered expr := by
  have h : evalF2Source expr := by
    cases expr with
    | ctorA =>
        simpa [evalF2Source, evalSource] using f2_of_A
    | ctorB v =>
        simpa [evalF2Source, evalSource] using f2_of_B v
  exact (evalF2_preserved expr).2 h

end Issue452
