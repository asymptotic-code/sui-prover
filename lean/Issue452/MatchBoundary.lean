import Issue452.Core
import Issue452.PureLowering

namespace Issue452

/-!
# MatchBoundary

This module documents the current proof boundary.

The Rust fix for `issue_452` establishes correct lowering for pure enum
constructor expressions, but it does **not** implement full pure lowering
for enum `match` / `VariantSwitch`. The main prover therefore reports the
constructive case as supported and the match case as unsupported.
-/

inductive ExtendedExpr where
  | ctorA
  | ctorB (v : Nat)
  | matchOn (e : E)
deriving DecidableEq, Repr

def supportedForLowering : ExtendedExpr → Prop
  | .ctorA => True
  | .ctorB _ => True
  | .matchOn _ => False

def lowerExtended : ExtendedExpr → Option E
  | .ctorA => some lowerPackVariantA
  | .ctorB v => some (lowerPackVariantB v)
  | .matchOn _ => none

theorem constructors_are_supported (expr : SourceExpr) :
    supportedForLowering
      (match expr with
      | .ctorA => .ctorA
      | .ctorB v => .ctorB v) := by
  cases expr <;> simp [supportedForLowering]

theorem enum_match_is_not_supported (e : E) :
    ¬ supportedForLowering (.matchOn e) := by
  simp [supportedForLowering]

theorem lowering_rejects_match (e : E) : lowerExtended (.matchOn e) = none := by
  simp [lowerExtended]

theorem lowering_accepts_supported_subset (expr : SourceExpr) :
    ∃ lowered, lowerExtended
      (match expr with
      | .ctorA => .ctorA
      | .ctorB v => .ctorB v) = some lowered := by
  cases expr with
  | ctorA =>
      exact ⟨lowerPackVariantA, by simp [lowerExtended]⟩
  | ctorB v =>
      exact ⟨lowerPackVariantB v, by simp [lowerExtended]⟩

theorem supported_subset_matches_core_lowering (expr : SourceExpr) :
    lowerExtended
      (match expr with
      | .ctorA => .ctorA
      | .ctorB v => .ctorB v) = some (lowerSource expr) := by
  cases expr <;> simp [lowerExtended, lowerSource]

end Issue452
