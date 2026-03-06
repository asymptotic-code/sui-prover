# CLAUDE.md - move-prover-boogie-backend

Boogie code generation and solver execution. Translates stackless bytecode to Boogie verification conditions and runs Z3.

## Overview

This crate generates Boogie verification conditions from analyzed Move bytecode and manages the Boogie/Z3 execution pipeline.

**Pipeline**: FunctionTargetsHolder → BoogieTranslator → .bpl file → Boogie → Z3 → Results

## Directory Structure

```
src/
├── lib.rs                      # Crate root (re-exports)
├── generator.rs                # Main orchestration (~1100 lines)
├── generator_options.rs        # Configuration structures
└── boogie_backend/
    ├── mod.rs                  # Module declarations
    ├── lib.rs                  # Prelude generation (~850 lines)
    ├── bytecode_translator.rs  # Core translator (~6100 lines)
    ├── spec_translator.rs      # Spec expression translation (~1400 lines)
    ├── boogie_wrapper.rs       # Boogie subprocess & output parsing (~2200 lines)
    ├── boogie_helpers.rs       # Name/type formatting utilities (~1100 lines)
    ├── options.rs              # BoogieOptions definition (~500 lines)
    ├── runner.rs               # Cross-platform process execution
    └── prelude/                # Boogie theory templates
        ├── prelude.bpl         # Main prelude (Tera template)
        ├── native.bpl          # Native function definitions
        ├── vector-*.bpl        # Vector theory variants
        ├── multiset-array-theory.bpl
        └── table-array-theory.bpl
```

## Key Entry Points

### generator.rs

```rust
// Main async verification function
pub async fn run_move_prover_with_model(
    env: &GlobalEnv,
    options: &BoogieOptions,
) -> BoogieResult;

// Generate Boogie code (returns CodeWriter)
pub fn generate_boogie(
    env: &GlobalEnv,
    options: &BoogieOptions,
    targets: &FunctionTargetsHolder,
) -> (CodeWriter, BiBTreeMap<Type, String>);

// Build and process bytecode targets
pub fn create_and_process_bytecode(
    env: &GlobalEnv,
    options: &BoogieOptions,
) -> FunctionTargetsHolder;
```

## Key Translators

### BoogieTranslator (bytecode_translator.rs)

Main orchestrator for bytecode-to-Boogie conversion:

```rust
pub struct BoogieTranslator<'env> {
    env: &'env GlobalEnv,
    options: &'env BoogieOptions,
    writer: &'env CodeWriter,
    spec_translator: SpecTranslator,
    targets: &'env FunctionTargetsHolder,
    types: &'env RefCell<BiBTreeMap<Type, String>>,
    asserts_mode: AssertsMode,
}
```

**Key methods**:
- `translate()` - Main entry, iterates modules/structs/functions
- `translate_spec()` - Generates spec conditions
- `translate_function_style()` - Core function translation

**Nested translators**:
- `FunctionTranslator` - Single function → Boogie procedure
- `StructTranslator` - Struct → Boogie type/validity functions
- `EnumTranslator` - Enum → Boogie variant/tag functions

### SpecTranslator (spec_translator.rs)

Translates Move spec expressions to Boogie:

```rust
// Handles: requires, ensures, invariants, quantifiers, choice expressions
// Lifts complex choice expressions into axiomatized functions
```

### BoogieHelpers (boogie_helpers.rs)

Name/type formatting utilities:
```rust
boogie_module_name(&module_env)     // "0x1_module_name"
boogie_struct_name(&struct_env)     // Type name with instantiation
boogie_function_name(&func_env)     // Procedure name
boogie_type(&ty)                    // u64 → $u64, Vec<T> → Vec T
boogie_temp(idx)                    // $t0, $t1, ...
boogie_field_sel(&field_env)        // Field accessor
```

## Prelude System

The prelude provides foundational Boogie definitions, generated via Tera templates.

### prelude.bpl
- Integer/bit-vector conversion functions
- Option<T> theory
- Vector operations (empty, push, pop, reverse)
- Quantifier helper axioms
- Type validity and equality functions

### native.bpl
- Bit-vector operations (SHL, SHR, AND, OR, XOR for u8-u256)
- Arithmetic functions (add, sub, mul, div, mod, pow, sqrt)
- Integer conversion functions

### Vector Theories
Select via `options.vector_theory`:
- `BoogieArray` - Standard Boogie array theory
- `SmtArray` - Z3's native array theory
- `SmtSeq` - Z3's sequence type
- `SmtArrayExt` - Array with extensionality axioms

## BoogieOptions (options.rs)

```rust
pub struct BoogieOptions {
    // Solver
    pub boogie_exe: String,
    pub z3_exe: String,
    pub vc_timeout: usize,

    // Verification strategy
    pub vector_theory: VectorTheory,
    pub native_equality: bool,
    pub stratification_depth: usize,

    // Modes
    pub spec_no_abort_check_only: bool,
    pub func_abort_check_only: bool,
    pub no_verify: bool,
    pub generate_only: bool,

    // Advanced
    pub custom_natives: Option<CustomNativeOptions>,
    pub prelude_extra: String,
    pub random_seed: usize,
    // ... many more
}
```

## AssertsMode

Controls how assertions are translated:
```rust
pub enum AssertsMode {
    Check,              // Normal assertions
    Assume,             // Assume instead of assert
    SpecNoAbortCheck,   // Only check spec no-abort
}
```

## Boogie Output Parsing (boogie_wrapper.rs)

### BoogieError
```rust
pub struct BoogieError {
    pub kind: BoogieErrorKind,  // Assertion/Inconclusive/Inconsistency
    pub loc: Loc,
    pub message: String,
    pub execution_trace: Vec<TraceEntry>,
    pub model: Option<Model>,
}
```

### TraceEntry
Counterexample information:
- `AtLocation(Loc)` - Source location
- `Temporary(String, String)` - Local variable value
- `Result(usize, String)` - Return value
- `Abort(String)` - Abort code
- `GlobalMem(QualifiedId<DatatypeId>, String)` - Memory state

## Data Flow

```
FunctionTargetsHolder (from move-stackless-bytecode)
    ↓
add_prelude() - Renders .bpl templates with type instantiations
    ↓
BoogieTranslator::translate()
├── StructTranslator - $IsValid, $IsEqual, accessors
├── EnumTranslator - tag, variant constructors
└── FunctionTranslator
    ├── Signature (params, returns)
    ├── Requires/Ensures (via SpecTranslator)
    └── Bytecode → Boogie statements
    ↓
CodeWriter (in-memory Boogie code)
    ↓
verify_boogie() - Write .bpl, call Boogie subprocess
    ↓
BoogieWrapper - Parse output, extract errors/model
    ↓
BoogieResult
```

## FileOptions

Per-verification-task configuration:
```rust
pub struct FileOptions {
    pub file_name: String,
    pub code_writer: CodeWriter,
    pub types: BiBTreeMap<Type, String>,
    pub boogie_options: Option<String>,
    pub timeout: Option<u64>,
    pub targets: FunctionTargetsHolder,
    pub qid: Option<QualifiedId<FunId>>,  // Single function mode
}
```

## Boogie File Modes

- `BoogieFileMode::Module` - Single .bpl per module (default)
- `BoogieFileMode::Function` - Separate .bpl per function (parallel verification)

## Remote Verification

Supports cloud-based verification via `RemoteOptions`:
```rust
pub struct RemoteOptions {
    pub url: String,
    pub api_key: String,
    pub concurrency: usize,
}
```

## Important Notes

1. **Prelude instantiation** - Types used in verification get Boogie functions generated
2. **Choice expressions** - Complex `some`/`choose` lifted to uninterpreted functions with axioms
3. **Process management** - BoogieWrapper handles timeout, process cleanup
4. **Parallel verification** - Multiple Boogie instances via `num_instances` option