# Sui Prover Changelog: July 2025 - February 2026

**Period**: July 10, 2025 - February 9, 2026
**Total Commits Analyzed**: 239
**Analysis Date**: February 9, 2026

---

## Executive Summary

Key achievements over this seven-month period:

- **Major Features**: Loop invariants, axiom functions, quantifier expansion (10+ types), pure function auto-detection, parallelized SMT solving
- **Performance**: 10x test speedup, SMT solver optimizations, dead code elimination
- **Verification**: 30+ critical bug fixes, enhanced type analysis, improved control flow
- **Infrastructure**: Claude Code integration, 3000+ lines of documentation, CI/CD modernization

---

## 📊 Quick Stats

| Metric | Count |
|--------|-------|
| Major Features | 18 |
| Critical Bug Fixes | 35 |
| Verification Improvements | 45 |
| Performance Optimizations | 8 |
| CI/CD Updates | 15 |
| Documentation Additions | 3000+ lines |
| Test Cases Added | 150+ |

---

## 🚀 Major Features

### Loop Invariants System (Nov 2025)
**Commit**: `812e8e269b` | **PR**: #280 | **Author**: andrii-a8c

External loop invariant specifications via `#[loop_invariant(...)]` macro. 1,204 insertions across 36 files, with new `move_loop_invariants.rs` module (370+ lines), error handling for 11 failure scenarios, and 13 test cases.

Enables verification of iterative code patterns critical for Sui smart contracts.

**Follow-ups**: `b1532dfd24` (rich error messages), `1c8b2de849` (New Old implementation), `bac6965fe1` (improved variable names)

---

### Axiom Functions (Dec 2025)
**Commit**: `b16623fd39` | **PR**: #401 | **Author**: andrii-a8c

Functions can be treated as uninterpreted/axiomatic in Boogie. 634 insertions across 32 files, new `axiom_function_analysis.rs` (126 lines), 8 test cases. Enables abstraction in verification without implementation details.

---

### Quantifier System Expansion (Aug-Jan)
**Author**: andrii-a8c

Major expansion of quantifier capabilities across multiple commits:

**Range-Based** (`660e1c85be`, Nov): Range/RangeMap support for efficient vector iteration, 25 test cases with native prelude functions.

**Aggregate** (Nov-Dec): SumMap + Count (`e14298ee27`), Filter + FindIndices (`7cdff5e2c1`), Sum slice (`0f15c81865`), Find/FindIndex macros (`52d93e650e`).

**Pure Quantifiers** (`ae00a79a3b`, Dec): Pure quantifier function support (1,180 insertions), enabling quantifier specs for pure functions without full Boogie verification.

Dramatically expanded verification expressiveness for collection operations.

---

### Auto Pure Function Detection (Dec 2025)
**Commit**: `8bd9e003fb` | **PR**: #361 | **Author**: andrii-a8c

Automatic detection and optimization of pure functions. 890 insertions across 80 files, new `pure_function_analysis.rs` (160 lines). Marks pure functions automatically without manual annotation, improving verification coverage and performance.

---

### Parallelized Boogie/Z3 SMT Solving (Oct 2025)
**Commit**: `f873d009b0` | **PR**: #218 | **Author**: andrii-a8c

Distributed verification via AWS Lambda. 1,793 insertions, new `lambda-boogie-handler` crate with Lambda HTTP handler (132 lines), ProverHandler with Redis caching (185 lines), Docker images, and async/await support. Enables scalability by distributing verification across Lambda instances.

---

### Control Flow Reconstruction (Nov 2025)
**Commit**: `e608720dcc` | **PR**: #289 | **Author**: Ethan Menell

Full if/else CFG reconstruction module. 2,790 insertions with 411-line reconstructor for structured control flow analysis. Enables more efficient Boogie generation and better readability.

---

### Conditional Merge Insertion (Sep 2025)
**Commit**: `16850cb2fb` | **PR**: #186 | **Author**: Rijnard van Tonder

Bytecode optimization pass for conditional branches. 927 insertions, new 443-line pass with 7 follow-up commits (multi-variable support, loop handling, fresh variables). Reduces bytecode complexity by merging conditional branches.

---

### Uninterpreted Functions (Jan 2026)
**Commit**: `f54f42f912` | **Authors**: Andrei Stefanescu, andrii-a8c

Support for uninterpreted functions via `#[ext(uninterpreted)]`. 306 insertions. Complements axiom functions, expanding the abstraction toolkit for verification.

---

### Move Standard Library Specifications (Jan 2026)
**Commit**: `f8dd6878d5` | **PR**: #444 | **Author**: Rijnard van Tonder

Comprehensive specs for Move stdlib. 1,206 insertions across 19 modules covering address, ascii, vectors, options, strings, integers (u8-u256), fixed-point. Foundational work for verifying contracts that use stdlib.

---

### Dynamic Field Analysis Enhancements (Jul-Oct 2025)

Expanded verification support for Sui's core dynamic field operations:
- `8a983d03e3` - Support for `dynamic_field::exists_`
- `787090e544` - Dynamic fields v2 handling
- `8619fbbe09` - Non-object dynamic fields
- `df70fcf30d` - Table/dynamic_field in pure functions

---

### No Abort Analysis & Deterministic Analysis (Sep 2025)

**No Abort Analysis** (`b8da8fdf3a`, #165): Detects functions that cannot abort, supports `#[ext(no_abort)]` and `#[ext(pure)]` attributes. 791 lines.

**Deterministic Analysis** (`515d62bab3`, #158): Detects deterministic function execution, enabling Boogie generation optimizations. 1,358 lines.

---

## 🐛 Critical Bug Fixes (Most Important & Tricky)

### 🔴 Z3 Quantifier Threshold Tuning (Nov 2025)
**Commit**: `0204d06185` | **PR**: #283 | **Author**: Cosmin Radoi

Z3 quantifier instantiation thresholds of 100 caused over-eager instantiation, false positives, and timeouts. Lowered `eager_threshold` to 10 and `lazy_threshold` to 20 (aligned with Z3 defaults). Small parameter change with massive verification impact.

---

### 🔴 Incorrect Boogie Generation for Equality in Pure Functions (Feb 2026)
**Commit**: `a19f558aa0` | **PR**: #480 | **Issue**: #462 | **Author**: Cosmin Radoi

Pure functions used direct `==`/`!=` in Boogie, which fails for non-extensional types like vectors. Fixed to use `$IsEqual` functions with proper type suffixes (e.g., `$IsEqual'vec'u64''(v1, v2)`). Without the fix, any pure function comparing complex types verified unsoundly.

---

### 🔴 Type Invariant Analysis Order Fix (Dec 2025)
**Commit**: `64f989e2a4` | **PR**: #390 | **Issue**: #366 | **Author**: andrii-a8c

Type invariant analysis ran AFTER dynamic field analysis, causing incorrect verification when invariants depended on dynamic field info. Reordered pipeline. Subtle ordering dependency where symptoms didn't point to root cause.

---

### 🔴 UID to Object Lookup with Alias Tracking (Oct 2025)
**Commit**: `4b0bb35679` | **PR**: #257 | **Issue**: #240 | **Author**: Andrei Stefanescu

UIDs passed through intermediate variables weren't tracked in dynamic field analysis. Integrated reaching definition analysis into type tracking, added `get_uid_object_type()` for alias chain resolution. Required combining multiple analysis passes with transitive variable assignment tracking.

---

### 🔴 Verification Analysis Pipeline Fix (Feb 2026)
**Commit**: `045d438191` | **PR**: #447 | **Author**: Andrei Stefanescu

In `func_abort_check_only` mode, SpecNoAbortCheck translated before Opaque, but datatype declarations only happened in Opaque style - causing Boogie compilation errors for tuple returns/mutable references. Also reorganized module spec vs function spec handling. Subtle issue that only manifested in specific verification configurations.

---

### 🔴 Dynamic Field IsValid Assertion (Jan 2026)
**Commit**: `24c9f499c8` | **Issue**: #450 | **Author**: msaaltink

Missing `IsValid` assertions for dynamic field operations allowed invalid accesses to verify successfully. Added assertions for both `remove` and read operations. Prevents unsound verification.

---

### 🔴 Quantifier Helper Type Inference Bug (Jan 2026)
**Commit**: `fd81571109` | **PR**: #440 | **Issue**: #439 | **Author**: andrii-a8c

Quantifier helpers inferred element types from return types, which was wrong for `FindIndices` (returns `Vec<u64>`, not Bool) and `Filter`. Fixed to check `QuantifierHelperType` enum variant explicitly. Type system bug where function semantics diverged from type signatures.

---

### 🔴 Fixed Mono Analysis for Vec Map (Jul 2025)
**Commits**: `1f654479e8`, `99f8d448d3` | **Authors**: andrii-a8c, d3mage

Monomorphism analysis incorrectly handled VecMap, causing type instantiation errors and verification failures across the Sui framework. Two iterations to fix.

---

### 🔴 Dynamic Field Pack Argument Bug (Aug 2025)
**Commit**: `e5e5e6d284` | **PR**: #134 | **Author**: d3mage

Dynamic field packing in Boogie was missing `EmptyTable()` arguments when constructing structs with dynamic fields. Fixed Pack instruction handler to extract field info and generate proper arguments. Required coordination between analysis passes and code generation.

---

### 🔴 Cross-Module Assert Handling (Dec 2025)
**Commit**: `9bc34b573b` | **PR**: #154 | **Author**: d3mage

Assertions across module boundaries weren't properly handled, causing multi-module verification failures. Reverted to original logic with added test cases.

---

### 🔴 Abort/Return Jump Deletion (Nov-Dec 2025)
**Commits**: `8f2fc18f5f` (#363), `7d4b5a043f` (#364) | **Author**: Andrei Stefanescu

Systematic removal of complex jump semantics from control flow representation. Removed AbortAction::Jump (-163 lines) and return jump patterns (-125 lines). Major architectural simplification requiring careful snapshot updates across 10+ files.

---

### 🔴 Split Asserts Handling (Nov 2025)
**Commit**: `61d53deb02` | **PR**: #343 | **Author**: Andrei Stefanescu

Introduced `AssertsMode` enum (Check/Assume) for separate assertion semantics. 481 insertions, major bytecode translator restructuring. Mixing modes incorrectly leads to unsound verification. Updated 11 snapshot files.

---

### 🔴 Recursion Protection (Dec 2025)
**Commit**: `271543fe2d` | **PR**: #395 | **Author**: andrii-a8c

New `recursion_analysis.rs` module (58 lines) detecting and protecting against infinite recursion that caused stack overflows during verification.

---

### 🔴 Remote Verification Error Handling (Jan 2026)
**Commit**: `c454f55505` | **PR**: #442 | **Author**: andrii-a8c

Remote verification panicked on network/file errors. Changed `RemoteProverResponse` to encode errors in the response struct itself with dedicated error handling. Essential for production reliability.

---

### Other Notable Fixes

- **`4e715339cc`** - Dynamic field analysis for reachable functions (#252, #237)
- **`474928fcc4`** - Control flow reconstruction edge case (#414)
- **`b5394c6a2f`** - Pattern match for new `run_on` field in VerificationAttribute
- **`ad1b677db4`** - Pipeline ordering bug (#416)
- **`492e45ff92`** - Quantifier type/logic fixes (#437, #435, #436)
- **`ac59e6408c`** - Target pipeline selection bug
- **`8dad4f1a81`** - Quantifiers typecheck generation
- **`f66b8eecbc`** - Pipeline call graph (#474)

---

## ✨ Verification Improvements

### Boogie Code Generation Enhancements

**Pure Function Translation** (`27ccd35e86`, Oct 2025): 816 insertions improving pure function handling; always use Boogie function form for pure callees (`705a071b48`).

**Dead Code Elimination** (Oct-Nov 2025): Four passes (`02cc9e82fd`, `18ae14fcb6`, `b9d949cfbd`, `2fa7e3dac6`) cutting dead Boogie code, opaque datatypes, and unused table instances. Reduced output size and sped up Z3 verification.

**Control Flow Improvements**: if-then-else instead of goto (`fc56dd52d3`, #369). See also backend-agnostic IR under [Refactoring](#-refactoring--code-quality).

---

### Spec Scope & Filtering

**Spec Scope Changes** (`131ce7d59d`, #348): PackageTargets system (707-line module) with multiple independent spec scopes and override support.

**Filtering System** (`fbac0fd74e`, Aug 2025): New `target_filter.rs` for selective verification on large projects.

**Filtering Redundant Dependencies** (`37da111740`, #148): 424 insertions eliminating redundant verification conditions across borrow, dynamic field, and verification analyses.

---

### Analysis Pass Improvements

- **`7d8de8f820`** (#321) - Full SSA support for candidate functions
- **`2fafbfc72d`** - Changed type invariant detection (371 insertions)
- **`5381620e78`** - Added more checks for invariants
- **`538b66a266`** (#284) - Cut redundant abort checks
- **`2c587378c6`** (#319) - Skip abort check in opaque functions that don't abort

---

### New Verification Capabilities

- **`f9a0c37467`** (#228) - Added sender spec
- **`f18ae14fcb6`** - Add `table::drop` intrinsic
- **`ed6f30034b`** - Native tx_context functions for pure function support
- **`50c69dae54`** - Extra BPL for items (custom Boogie code)

---

## ⚡ Performance Optimizations

### 🏆 10x Test Speedup (Feb 2026)
**Commit**: `bd83cbefd1` | **PR**: #486 | **Author**: Cosmin Radoi

Integration tests were serialized by a global PackageLock (314 tests, ~30 minutes). Created `move_model_for_package_legacy_unlocked()` for tests running in isolated tempdirs. Full suite: ~30 min to ~2-4 min (**10x speedup**).

---

### Test Suite Parallelization (Aug 2025)
**Commit**: `9ba18982aa` | **PR**: #146 | **Author**: chameco

Split Insta tests into individual cargo test targets using `dir-test` macro. ~15 min to ~5 min (**3x speedup**).

---

### Vector Generation Optimization (Jan 2026)
**Commit**: `56fbce9381` | **PR**: #432 | **Author**: andrii-a8c

Adaptive vector construction based on theory selection (SmtSeq vs array-based). Reduced verification time for array-based theories.

---

### Other Performance Improvements

- **`d7538ab227`** (#443) - Range optional BPL generation (conditional prelude)
- **`802921e77b`** (#233) - Remove unneeded passes (6 passes eliminated)
- **`56d8c5a0ed`** (#152) - Improved Boogie generation (code cleanup)

---

## 🔧 CI/CD & Infrastructure

### Claude Code Integration (Feb 2026)

3000+ lines of documentation: root CLAUDE.md (`022a8861c2`, #491), per-crate CLAUDE.md files (`26f4edd8a4`, #492; `2b77a728d4`, #493). Six commits building sui-prover skill (`5415e5fde3` → `44090e8002`), integrating specs, FAQ, prover reference, and migrating RUNNING_PROVER.md to skills. GitHub workflow (`1997f053d1`, #479).

---

### CI Pipeline Improvements

**Test Infrastructure**: CI test jobs split (`57c28279b4`), Insta test parallelization (`9ba18982aa`, #146), divided internal tests into 2 jobs (`2cd2804d4b`, #341).

**Workflow Updates**: Two-stage CI build (`ff82d88991`, #259), Ika BPL generation (`5ae08e379f`, #306), .NET 8 compatibility (`db798adac8`, #453), self-hosted runners (`1a3848d2a7`, #485).

**Code Quality**: Cargo check action (`cc3fa84834`, #302), Rustfmt action (`b2e68f2ef0`, #297, 2,994 insertions).

---

### Environment & Dependencies

Abort on missing CVC5_EXE/Z3_EXE (`fbee61e319`, #122), case-sensitive filesystem fix (`27666f83ff`, #121), two Sui version updates (`f931b35845` #112, `567fa674a7` #340), env var for builtin package loading (`9104ef51ef`, #445).

---

## 📚 Documentation & Developer Experience

**Contributing**: Updated CONTRIBUTING.md (`3b71749610`, #150) and README (`6e7a041273`, #141).

**Debugging & Diagnostics**: Spec calls tree logging (`f1790392d1`, #308), spec dependency display (`6eb8b64c90`, #455), dump bytecode option (`214bd6bfc0`, #157).

**Statistics**: Function statistics for public functions without specs (`1a2c10d003`, #298), result printing updates (`5df49478f3`, #310).

**Specification Libraries**: Move stdlib specs (`f8dd6878d5`, #444, 1,206 lines across 19 modules), additional specs (`9d11008eb8`, #192, 574 ins across 35 files).

---

## 🔨 Refactoring & Code Quality

### Major Architectural Changes

**Backend-Agnostic IR** (`e980f0b0e5`, #353, Dec): Created intermediate-theorem-format crate (6,174 insertions, 4,781 deletions). Later simplified by removing unused crates (`15e377484f`, #477, Jan - 6,227 deletions across 57 files).

**New Verification Flow** (`5137bc5f2e`, #449, Jan): Restructured verification_analysis.rs (391 insertions, 380 deletions), improved analyses across the pipeline.

---

### Code Organization

**Conditional Merge Reimplementation** (`1cd1f1d871`, #413, Dec): Simplified from 744 lines, updated 29 snapshot tests.

**Separated Prover Options** (`828d77916e`, #265, Oct): Moved options from global state to per-crate config for thread-safety and testability.

**Options Refactoring** (`b47c3b82af`, #155, Dec): Unified preprocessing, cleaned up filtering code.

---

### Utility Additions

- **`222bf68faa`** (#412, Dec) - Bytecode dest/src helpers
- **`40517ac832`** (#405, Dec) - Don't emit trace if --no-counterexample-trace
- **`22a8f788e0`** (Dec) - Added include per function
- **`2cf28b50f1`** (#262, Oct) - External API for topological ordering

---

## 🎯 Notable Test & Feature Additions

### Test Coverage Expansion

**Quantifiers & Macros**: Vector macro tests (`69b41835e9`), loop computation proofs (`0a30615eb3`), conditional end-to-end tests (`ba96d79de8`, #226).

**Issue Regression Tests**: #102, #103, #145, #237, #240, #355, #362, #366, #414, #415, #416, #435, #436, #450, #462.

**Test Infrastructure**: Suppressed Boogie printout in tests (`3d43fe1db9`, 40 snapshots cleaned), added conditional snapshots (`36d28bc81c`).

---

### Feature Flags & CLI Additions

- **`3baa1c734f`** (#489, Feb) - `--skip-fun-no-abort` flag
- **`e5672cba81`** (#303, Nov) - `--force-timeout` flag
- **`0fd410c6fd`** (#358, Nov) - Skip version check flag
- **`eb57cc9bf5`** (Dec) - Auto spec no abort check with focus/filter

---

## 📈 Commit Statistics by Period

| Period | Commits | Key Focus |
|--------|---------|-----------|
| Jul 10-30, 2025 | 16 | Foundation: VecMap fixes, object ID native impl, Sui version update |
| Jul 31-Aug 20, 2025 | 11 | Filtering, vector functions, dynamic field fixes, test parallelization |
| Aug 21-Sep 10, 2025 | 7 | Deterministic & no-abort analysis, improved Boogie generation |
| Sep 11-Oct 1, 2025 | 22 | Conditional merge insertion (7 commits), dynamic field expansion |
| Oct 2-22, 2025 | 13 | Parallelized SMT solving, macro quantifiers, UID lookup fixes |
| Oct 23-Nov 12, 2025 | 44 | **MOST ACTIVE**: Loop invariants, quantifier expansion, abort optimization |
| Nov 13-Dec 3, 2025 | 16 | Range quantifiers, sum slice, control flow reconstruction |
| Dec 4-24, 2025 | 40 | Axiom functions, pure quantifiers, recursion protection |
| Dec 25-Jan 14, 2026 | 11 | Move stdlib specs, quantifier fixes, remote error handling |
| Jan 15-Feb 9, 2026 | 34 | **10x test speedup**, uninterpreted functions, Claude Code integration |

---

## 🏆 Most Impactful Changes

### By Lines Changed
1. **Backend-Agnostic IR + Simplification** (`e980f0b0e5`, `15e377484f`) - 6,174 ins / 6,227 del
2. **Control Flow Reconstruction** (`e608720dcc`) - 2,790 insertions
3. **Rustfmt Pass** (`b2e68f2ef0`) - 2,994 insertions
4. **Parallelized SMT Solving** (`f873d009b0`) - 1,793 insertions

### By Complexity & Risk
1. **Split Asserts Handling** (#343) - Complex semantics, high risk
2. **Abort/Return Jump Deletion** (#363, #364) - Architectural simplification
3. **Type Invariant Analysis Order** (#390, #366) - Subtle pipeline dependency
4. **Verification Analysis Pipeline** (#447) - Core verification logic
5. **UID to Object Lookup** (#257, #240) - Multi-pass analysis coordination

### By Performance Impact
1. **10x Test Speedup** (#486) - 30 min → 2-4 min
2. **3x Test Speedup** (#146) - 15 min → 5 min
3. **Z3 Threshold Tuning** (#283) - Small change, big SMT impact
4. **Parallelized SMT** (#218) - Scalability infrastructure
5. **Dead Code Elimination** (4 commits) - Reduced verification overhead

---

## 👥 Top Contributors

| Contributor | Commits | Key Areas |
|-------------|---------|-----------|
| **andrii-a8c** | 80+ | Quantifiers, loop invariants, axiom functions, features |
| **Andrei Stefanescu** | 45+ | Critical fixes, verification logic, control flow |
| **Cosmin Radoi** | 30+ | Performance, infrastructure, Claude Code integration |
| **Rijnard van Tonder** | 20+ | Conditional merge, stdlib specs, control flow |
| **d3mage** | 15+ | Bug fixes, filtering, analysis improvements |
| **Ethan Menell** | 2 | Control flow reconstruction |
| **msaaltink** | 5+ | Test coverage, dynamic field fixes |
| **Danilych Warden** | 5+ | Documentation, stats, CI improvements |
| **chameco** | 3+ | Test infrastructure, environment fixes |

---

## 🎉 Conclusion

Exceptional progress: dramatically expanded verification (loop invariants, axioms, quantifiers, pure functions), orders-of-magnitude performance gains (10x test speedup, SMT optimizations), 35+ soundness bug fixes, comprehensive documentation with Claude Code integration, and architectural simplification with parallel SMT scaling.

---

*Generated on February 9, 2026 from comprehensive analysis of 239 commits*
