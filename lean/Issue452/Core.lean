namespace Issue452

/-!
# Core

This file contains the smallest semantic core needed to talk about the
`issue_452` fix:

- a tiny enum with two constructors
- the witness predicate corresponding to the repro helper
- the top-level pure predicate
- basic completeness and equivalence lemmas
-/

inductive E where
  | A
  | B (v : Nat)
deriving DecidableEq, Repr

/-! ## Source-level predicates -/

def isB (v : Nat) : E → Prop
  | .B w => w = v
  | .A => False

def f2 (e : E) : Prop :=
  e = .A ∨ ∃ v, isB v e

def lowerPackVariantA : E :=
  .A

def lowerPackVariantB (v : Nat) : E :=
  .B v

theorem lowerPackVariantA_sound : lowerPackVariantA = E.A := rfl

theorem lowerPackVariantB_sound (v : Nat) : lowerPackVariantB v = E.B v := rfl

theorem isB_iff_eq_B (v : Nat) (e : E) : isB v e ↔ e = .B v := by
  cases e with
  | A =>
      simp [isB]
  | B w =>
      simp [isB]

theorem f2_of_A : f2 .A :=
  Or.inl rfl

theorem f2_of_B (v : Nat) : f2 (.B v) :=
  Or.inr ⟨v, rfl⟩

/-! ## Completeness and lowered-view lemmas -/

theorem constructor_cases_complete (e : E) : e = .A ∨ ∃ v, e = .B v := by
  cases e with
  | A =>
      exact Or.inl rfl
  | B v =>
      exact Or.inr ⟨v, rfl⟩

theorem f2_total (e : E) : f2 e := by
  rcases constructor_cases_complete e with hA | ⟨v, hB⟩
  · simpa [hA] using f2_of_A
  · simpa [hB] using f2_of_B v

def loweredF2 (e : E) : Prop :=
  e = lowerPackVariantA ∨ ∃ v, e = lowerPackVariantB v

theorem loweredF2_iff_f2 (e : E) : loweredF2 e ↔ f2 e := by
  constructor
  · intro h
    rcases h with hA | ⟨v, hB⟩
    · cases hA
      simpa [lowerPackVariantA] using f2_of_A
    · cases hB
      simpa [lowerPackVariantB] using f2_of_B v
  · intro h
    rcases constructor_cases_complete e with hA | ⟨v, hB⟩
    · exact Or.inl hA
    · exact Or.inr ⟨v, hB⟩

theorem f2_of_lowered_pack_variant (v : Nat) : f2 (lowerPackVariantB v) := by
  simpa [lowerPackVariantB] using f2_of_B v

theorem exists_witness_roundtrip (v : Nat) : ∃ witness, isB witness (.B v) := by
  exact ⟨v, rfl⟩

theorem lowered_exists_witness_roundtrip (v : Nat) :
    ∃ witness, isB witness (lowerPackVariantB v) := by
  simpa [lowerPackVariantB] using exists_witness_roundtrip v

theorem lowerPackVariant_preserves_f2 (v : Nat) :
    loweredF2 (lowerPackVariantB v) ∧ f2 (lowerPackVariantB v) := by
  constructor
  · exact Or.inr ⟨v, rfl⟩
  · exact f2_of_lowered_pack_variant v

end Issue452
