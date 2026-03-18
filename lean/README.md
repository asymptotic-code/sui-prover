# Lean 4 Showcase

This directory is a small, separate Lean 4 proof showcase for `issue_452`.

It does **not** replace the main Boogie/Z3 verification pipeline. Instead, it demonstrates a
machine-checked proof of the core enum-construction idea behind the fix:

- model a tiny enum `E = A | B Nat`
- model the pure helper predicate shape used in the repro
- prove that lowering a packed enum variant into a direct constructor expression is sound
- prove that `f2 (E.B v)` holds with an explicit existential witness
- prove constructor-case completeness for the tiny enum model
- prove an equivalence between the lowered representation and the source-level predicate

## Files

- `lean/Issue452.lean` — root export module
- `lean/Issue452/Core.lean` — tiny enum model and base theorems
- `lean/Issue452/PureLowering.lean` — lowering-preservation proofs
- `lean/Issue452/QuantifierView.lean` — `exists!`-style witness proofs
- `lean/Issue452/MatchBoundary.lean` — explicit unsupported-boundary statement for pure enum `match`
- `lean/lakefile.toml` — minimal Lake project config
- `lean/lean-toolchain` — pinned Lean 4 toolchain
- `lean/ProofToCode.md` — Rust ↔ Lean concept mapping

## Suggested local commands

```powershell
cd lean
lake build
```

If `lake` is not on the current shell `PATH`, open a new terminal after the user-level environment
changes, or invoke it via `C:\Users\peter\.elan\bin\lake.exe`.

## Main theorems

- `isB_iff_eq_B`
- `constructor_cases_complete`
- `f2_total`
- `loweredF2_iff_f2`
- `lowerPackVariant_preserves_f2`
- `lowerSource_sound`
- `evalIsB_preserved`
- `evalF2_preserved`
- `lowering_preserves_totality`
- `quantifier_view_preserved`
- `quantified_branch_matches_f2`
- `lowered_quantifier_is_constructive`
- `enum_match_is_not_supported`
- `lowering_rejects_match`
- `supported_subset_matches_core_lowering`
