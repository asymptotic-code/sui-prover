# Proof-to-Code Mapping

This note connects the small Lean 4 showcase to the concrete Rust fix for `issue_452`.

## Goal

Show that the Lean proofs are not random toy lemmas, but a compact semantic mirror of the real fix:

- Rust fixes pure lowering of enum variant constructors
- Lean proves that constructor-based lowering preserves the intended witness-oriented meaning

## Rust → Lean correspondence

| Rust / prover concept | Lean counterpart | Why it matters |
| --- | --- | --- |
| `Operation::PackVariant` in pure lowering | `SourceExpr.ctorA` / `SourceExpr.ctorB` | Represents source-level enum construction |
| enum value `E::A` / `E::B(v)` | `Issue452.E.A` / `Issue452.E.B v` | Shared semantic object |
| pure helper `is_b(v, e)` | `isB v e` | The witness predicate from the repro |
| pure helper `f2(e)` | `f2 e` | The top-level property used in the regression |
| lowering to a constructor expression | `lowerSource` | The semantic act being justified |
| "lowered program means the same thing" | `lowerSource_sound` / `evalF2_preserved` | Core soundness story |
| existential witness in `exists!` branch | `hasIsBWitness` | Captures the quantifier-facing view |
| constructor lowering still provides a witness | `quantifier_view_preserved` | Explains why the repro should stop panicking |
| current unsupported pure enum `match` lowering | `MatchBoundary` module | Makes the proof boundary explicit |

## File mapping

- `crates/move-prover-boogie-backend/src/boogie_backend/bytecode_translator.rs`
  - Rust implementation of the `PackVariant` pure lowering fix
- `lean/Issue452/Core.lean`
  - Minimal semantic model of the enum and the `f2` property
- `lean/Issue452/PureLowering.lean`
  - Proof that constructor lowering preserves the source meaning
- `lean/Issue452/QuantifierView.lean`
  - Proof that the existential witness view is preserved
- `lean/Issue452/MatchBoundary.lean`
  - Proof-oriented statement of the current unsupported boundary

## Reading order

1. `Core.lean`
2. `PureLowering.lean`
3. `QuantifierView.lean`
4. `MatchBoundary.lean`

## What this does **not** claim

- It does not replace the Boogie/Z3 prover.
- It does not prove the whole Sui Prover pipeline correct.
- It does not prove pure enum `match` lowering, because the current Rust code still reports that as unsupported.

## What it *does* claim

- The central `issue_452` fix has a clean semantic story.
- Constructor-based lowering is the right shape for the supported subset.
- The witness-producing branch used by the repro remains meaningful after lowering.
