import Issue452.Core
import Issue452.PureLowering

namespace Issue452

/-!
`exists!`-style view specialized to the tiny `issue_452` model.
We separate the quantifier-facing statement from the lower-level
constructor-preservation statements so the showcase reads more like
an appendix: first define the witness shape, then prove it is preserved.
-/

/-! ## Witness-oriented quantifier view -/
def hasIsBWitness (e : E) : Prop :=
  ∃ witness, isB witness e

def hasIsBWitnessSource : SourceExpr → Prop :=
  hasIsBWitness ∘ evalSource

def hasIsBWitnessLowered : SourceExpr → Prop :=
  hasIsBWitness ∘ lowerSource

theorem witness_for_ctorB_source (v : Nat) : hasIsBWitnessSource (.ctorB v) := by
  refine ⟨v, ?_⟩
  simp [evalSource, isB]

theorem no_witness_for_ctorA_source : ¬ hasIsBWitnessSource .ctorA := by
  intro h
  rcases h with ⟨witness, hwitness⟩
  simp [evalSource, isB] at hwitness

theorem witness_for_ctorB_lowered (v : Nat) : hasIsBWitnessLowered (.ctorB v) := by
  refine ⟨v, ?_⟩
  simp [lowerSource, lowerPackVariantB, isB]

theorem no_witness_for_ctorA_lowered : ¬ hasIsBWitnessLowered .ctorA := by
  intro h
  rcases h with ⟨witness, hwitness⟩
  simp [lowerSource, lowerPackVariantA, isB] at hwitness

theorem quantifier_view_preserved (expr : SourceExpr) :
    hasIsBWitnessLowered expr ↔ hasIsBWitnessSource expr := by
  cases expr with
  | ctorA =>
      simp [hasIsBWitnessLowered, hasIsBWitnessSource, hasIsBWitness, lowerSource, evalSource,
        lowerPackVariantA, isB]
  | ctorB v =>
      simp [hasIsBWitnessLowered, hasIsBWitnessSource, hasIsBWitness, lowerSource, evalSource,
        lowerPackVariantB, isB]

theorem quantified_branch_matches_f2 (expr : SourceExpr) :
    evalF2Lowered expr ↔ (evalSource expr = .A ∨ hasIsBWitnessLowered expr) := by
  cases expr with
  | ctorA =>
      simp [evalF2Lowered, f2, lowerSource, evalSource, hasIsBWitnessLowered, hasIsBWitness,
        lowerPackVariantA, isB]
  | ctorB v =>
      simp [evalF2Lowered, f2, lowerSource, evalSource, hasIsBWitnessLowered, hasIsBWitness,
        lowerPackVariantB, isB]

theorem lowered_quantifier_is_constructive (expr : SourceExpr) :
    hasIsBWitnessLowered expr → ∃ witness, lowerSource expr = .B witness := by
  intro h
  cases expr with
  | ctorA =>
      exfalso
      exact no_witness_for_ctorA_lowered h
  | ctorB v =>
      exact ⟨v, by simp [lowerSource, lowerPackVariantB]⟩

end Issue452
