# CLAUDE.md - move-stackless-bytecode

Bytecode transformation and analysis passes. Converts Move stack-based bytecode to stackless 3-address form and runs 30+ analysis passes.

## Overview

This crate transforms Move bytecode into a stackless representation suitable for verification, then runs an ordered pipeline of analysis passes that annotate functions with verification-relevant information.

**Pipeline**: Move Bytecode → Stackless Bytecode → Analysis Passes → Annotated FunctionTarget

## Directory Structure

```
src/
├── stackless_bytecode.rs           # Core bytecode types (Bytecode, Operation, Label)
├── stackless_bytecode_generator.rs # Move bytecode → stackless conversion
├── function_target.rs              # FunctionTarget, FunctionData types
├── function_target_pipeline.rs     # Pipeline orchestration, FunctionTargetsHolder
├── package_targets.rs              # Selects functions to verify from #[spec(prove)]
├── pipeline_factory.rs             # Pipeline construction with all passes
├── options.rs                      # ProverOptions configuration
├── annotations.rs                  # Type-safe annotation storage
├── ast.rs                          # Spec language AST (Exp, ConditionKind)
├── dataflow_analysis.rs            # Generic dataflow framework
├── dataflow_domains.rs             # Abstract domains for dataflow
├── [30+ analysis pass files]       # Individual analysis implementations
└── helpers/                        # Utility helpers
```

## Key Types

### FunctionTarget (function_target.rs)
Wrapper around `FunctionEnv` with rewritten bytecode and analysis results:
```rust
// Get target from holder
let target = targets.get_target(&func_env, &FunctionVariant::Baseline);

// Access bytecode
for bc in target.get_bytecode() { ... }

// Access annotations from analysis passes
let info = target.get_annotations().get::<VerificationInfo>();
let liveness = target.get_annotations().get::<LiveVarAnnotation>();
```

### FunctionData (function_target.rs)
Persistent storage for function analysis results:
```rust
pub struct FunctionData {
    pub variant: FunctionVariant,      // Baseline or Verification
    pub code: Vec<Bytecode>,           // Transformed bytecode
    pub local_types: Vec<Type>,        // Locals including parameters
    pub return_types: Vec<Type>,
    pub locations: BTreeMap<AttrId, Loc>,
    pub annotations: Annotations,      // Analysis results
    pub loop_invariants: BTreeSet<AttrId>,
    // ... more fields
}
```

### FunctionVariant (function_target_pipeline.rs)
```rust
pub enum FunctionVariant {
    Baseline,                          // Original bytecode
    Verification(VerificationFlavor),  // Instrumented for verification
}
```

### FunctionTargetsHolder (function_target_pipeline.rs)
Central container for all function targets:
```rust
// Get/modify targets
let target = targets.get_target(&func_env, &variant);
let data = targets.remove_target_data(&id, &variant);
targets.insert_target_data(&id, variant, data);

// Access PackageTargets (verification selection)
let pkg_targets = targets.get_package_targets();
```

### PackageTargets (package_targets.rs)
Selects which functions to verify based on annotations:
- `#[spec(prove)]` - Functions to verify
- `#[ext(pure)]`, `#[ext(no_abort)]` - External function attributes

## Stackless Bytecode (stackless_bytecode.rs)

```rust
pub enum Bytecode {
    Assign(AttrId, TempIndex, TempIndex, AssignKind),
    Call(AttrId, Vec<TempIndex>, Operation, Vec<TempIndex>, Option<AbortAction>),
    Ret(AttrId, Vec<TempIndex>),
    Load(AttrId, TempIndex, Constant),
    Branch(AttrId, Label, Label, TempIndex),  // if-then-else
    Jump(AttrId, Label),
    Label(AttrId, Label),
    Abort(AttrId, TempIndex),
    Nop(AttrId),
    SpecBlock(AttrId, SpecBlockId),  // Spec conditions
    // ...
}

pub enum Operation {
    Function(ModuleId, FunId, Vec<Type>),  // Function call
    BorrowLoc, BorrowGlobal, BorrowField,
    ReadRef, WriteRef,
    Pack, Unpack,
    // ... arithmetic, comparison, etc.
}
```

## Analysis Pipeline

Passes run in order defined in `pipeline_factory.rs`:

### Early Analysis
1. **VerificationAnalysisProcessor** - Determines what to verify/inline
2. **RecursionAnalysisProcessor** - Identifies recursive functions
3. **SpecGlobalVariableAnalysisProcessor** - Analyzes spec globals
4. **SpecPurityAnalysis** - Determines pure functions
5. **DebugInstrumenter** - Adds debug info

### Core Transformations
6. **EliminateImmRefsProcessor** - Removes immutable refs
7. **MutRefInstrumenter** - Instruments mutable refs
8. **NoAbortAnalysisProcessor** - Determines which functions can't abort
9. **DeterministicAnalysisProcessor** - Analyzes determinism
10. **DynamicFieldAnalysisProcessor** - Handles Sui dynamic fields
11. **MoveLoopInvariantsProcessor** - Processes loop invariants
12. **TypeInvariantAnalysisProcessor** - Analyzes type invariants

### Dataflow Analysis
13-18. **ReachingDefProcessor**, **LiveVarAnalysisProcessor**, **BorrowAnalysisProcessor**, **MemoryInstrumentationProcessor** (with reruns)

### Optimization & Final
19. **ConditionalMergeInsertionProcessor** - Merges conditional branches
20. **CleanAndOptimizeProcessor** - Dead code elimination
21-27. **UsageProcessor**, **SpecWellFormedAnalysisProcessor**, **QuantifierIteratorAnalysisProcessor**, **ReplacementAnalysisProcessor**, **PureFunctionAnalysisProcessor**, **AxiomFunctionAnalysisProcessor**, **LoopAnalysisProcessor**

### Instrumentation
28-31. **SpecInstrumentationProcessor**, **WellFormedInstrumentationProcessor**, **MonoAnalysisProcessor**, **NumberOperationProcessor**

## Annotations System (annotations.rs)

Type-safe, extensible storage for analysis results:
```rust
// Store annotation
data.annotations.set::<LiveVarAnnotation>(liveness);

// Retrieve annotation
let liveness = target.get_annotations().get::<LiveVarAnnotation>();
```

## FunctionTargetProcessor Trait

All analysis passes implement this:
```rust
pub trait FunctionTargetProcessor {
    fn process(
        &self,
        targets: &mut FunctionTargetsHolder,
        func_env: &FunctionEnv,
        data: FunctionData,
        scc_opt: Option<&[FunctionEnv]>,  // For recursive functions
    ) -> FunctionData;

    fn name(&self) -> String;
    fn initialize(&self, env: &GlobalEnv, targets: &mut FunctionTargetsHolder) {}
    fn finalize(&self, env: &GlobalEnv, targets: &mut FunctionTargetsHolder) {}
}
```

## Running the Pipeline

```rust
use move_stackless_bytecode::pipeline_factory::default_pipeline_with_options;

let pipeline = default_pipeline_with_options(&options);
pipeline.run(env, &mut targets);
```

## Spec Language AST (ast.rs)

```rust
pub enum ConditionKind {
    Assert, Assume,
    Requires, Ensures, AbortsIf,
    LoopInvariant, GlobalInvariant,
    // ...
}

pub enum Exp {
    Value(NodeId, Value),
    LocalVar(NodeId, Symbol),
    Call(NodeId, Operation, Vec<Exp>),
    Quant(NodeId, QuantKind, Vec<LocalVarDecl>, Vec<Vec<Exp>>, Option<Exp>, Exp),
    // ...
}
```

## ProverOptions (options.rs)

Key configuration affecting the pipeline:
```rust
pub struct ProverOptions {
    pub generate_only: bool,
    pub skip_loop_analysis: bool,
    pub skip_spec_no_abort: bool,
    pub skip_fun_no_abort: bool,
    pub dump_bytecode: Option<String>,
    // ... many more
}
```

## Important Notes

1. **Pipeline order matters** - Passes depend on results from previous passes
2. **SCC handling** - Recursive functions processed together for consistency
3. **Multiple variants** - Functions can have Baseline and Verification variants
4. **Memory safety** - Borrow analysis critical for correct verification conditions