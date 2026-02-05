# CLAUDE.md - move-model

Semantic model of Move code. Builds and represents the type-checked AST with full type information.

## Overview

This crate transforms Move source code into a semantic model (`GlobalEnv`) containing modules, functions, structs, enums, and specifications with resolved types and locations.

**Pipeline**: Move Source → Compiler (parse/type-check) → ModelBuilder → GlobalEnv

## Directory Structure

```
src/
├── lib.rs              # Entry points: run_model_builder(), run_spec_checker()
├── model.rs            # Core types: GlobalEnv, ModuleEnv, FunctionEnv, etc. (~6500 lines)
├── ty.rs               # Type system: Type enum, PrimitiveType, Substitution (~1300 lines)
├── symbol.rs           # Symbol pool for interned strings
├── ast.rs              # AST for spec language: Attribute, Value, ModuleName
├── pragmas.rs          # Pragma handling
├── code_writer.rs      # Code generation utilities
├── well_known.rs       # Well-known module/function names
└── builder/
    ├── model_builder.rs    # ModelBuilder: orchestrates model construction
    ├── module_builder.rs   # ModuleBuilder: translates individual modules
    └── exp_translator.rs   # ExpTranslator: translates expressions
```

## Core Types Hierarchy

```
GlobalEnv (root container)
├── SymbolPool           # Interned strings
├── source_files         # Source file registry
├── module_data[]        # All loaded modules
│   └── ModuleData
│       ├── struct_data  # BTreeMap<DatatypeId, StructData>
│       ├── enum_data    # BTreeMap<DatatypeId, EnumData>
│       ├── function_data # BTreeMap<FunId, FunctionData>
│       └── named_constants
└── exp_info             # NodeId → (Loc, Type) mapping
```

## Key Types

### GlobalEnv (model.rs)
Root environment containing all data:
```rust
// Access patterns
let module_env = global_env.get_module(module_id);
let func_env = module_env.get_function(func_id);
let struct_env = module_env.get_struct(struct_id);

// Node tracking
let node_id = global_env.new_node_id();
let loc = global_env.get_node_loc(node_id);
let ty = global_env.get_node_type(node_id);

// Target modules (non-dependency)
for module in global_env.get_target_modules() { ... }
```

### ModuleEnv, FunctionEnv, StructEnv
Lightweight reference wrappers providing read access:
```rust
let module_env: ModuleEnv<'_> = global_env.get_module(id);
let func_env: FunctionEnv<'_> = module_env.get_function(func_id);
let struct_env: StructEnv<'_> = module_env.get_struct(struct_id);

// Key methods
func_env.get_bytecode()      // Move bytecode instructions
func_env.get_parameters()    // Parameter list
struct_env.get_fields()      // Field iterator
struct_env.get_abilities()   // Copy, Drop, Store, Key
```

### Type (ty.rs)
```rust
pub enum Type {
    Primitive(PrimitiveType),  // Bool, U8, U64, Address, etc.
    Vector(Box<Type>),
    Datatype(ModuleId, DatatypeId, Vec<Type>),  // Struct/Enum
    Reference(bool, Box<Type>),  // bool = is_mutable
    TypeParameter(u16),
    Tuple(Vec<Type>),
    Fun(Vec<Type>, Box<Type>),   // Spec-only function type
    Error, Var(u16),             // Temporary during type inference
}
```

### Identifiers
- `ModuleId(RawIndex)` - Index-based for fast Vec access
- `DatatypeId(Symbol)` - Symbol-based for struct/enum
- `FunId(Symbol)` - Function identifier
- `FieldId(Symbol)` - Field identifier
- `NodeId(usize)` - AST node identifier
- `QualifiedId<Id>` - Id qualified by module

## Model Building Process

1. **Compiler Pipeline** (lib.rs)
   - Parser → Expansion → Typing → Compilation
   - Collects diagnostics

2. **Spec Checking** (lib.rs)
   - Creates ModelBuilder with mutable GlobalEnv
   - Iterates modules in dependency order

3. **Module Translation** (module_builder.rs)
   - Declaration analysis: register structs, enums, functions
   - Definition analysis: type-check bodies
   - Population: add to GlobalEnv

## Entry Points

```rust
// Build model from source files
let env = run_model_builder(targets, deps, named_address_map, options)?;

// Build model from compiled modules
let env = run_bytecode_model_builder(modules)?;

// Access modules
for module in env.get_modules() {
    for func in module.get_functions() {
        println!("{}", func.get_name());
    }
}
```

## Symbol Pool

All strings are interned for fast comparison:
```rust
let symbol = env.symbol_pool().make("my_name");
let name = env.symbol_pool().string(symbol);
```

## Well-Known Names

The crate defines well-known identifiers for:
- Prover modules: "prover", "ghost", "vector_iter"
- Spec functions: requires, ensures, asserts, invariant, global
- Sui framework: object, dynamic_field, event, transfer
- Standard library: vector, option, table

## Important Design Patterns

1. **Reference-based access**: `ModuleEnv`, `FunctionEnv` are references, not owned data
2. **Lazy caching**: Call graphs computed on first access via `RefCell<Option<_>>`
3. **Source mapping**: `FileId` → codespan Files database for error reporting
4. **Extensions**: `BTreeMap<TypeId, Box<dyn Any>>` for tool-specific data

## Common Access Patterns

```rust
// Get qualified function ID
let qid = func_env.get_qualified_id();

// Check if function is native
if func_env.is_native() { ... }

// Get struct fields by name
if let Some(field) = struct_env.find_field(symbol) { ... }

// Check abilities
if struct_env.has_memory() { ... }  // Key ability

// Iterate dependencies
for dep_id in module_env.get_dependencies() { ... }
```