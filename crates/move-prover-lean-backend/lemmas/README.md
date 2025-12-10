# Sui Prover Lemma Library

This directory contains the **Sui Prover Lemma Monorepo** - a collection of proven lemmas that can be reused across Move verification projects.

## Structure

```
lemmas/
├── Universal/              # Cross-cutting lemmas available to all projects
│   ├── Arithmetic/        # Basic arithmetic properties
│   ├── Bitwise/          # Bitwise operation properties
│   ├── Monotonicity/     # Monotonicity lemmas
│   ├── ProgramState/     # ProgramState monad lemmas
│   └── Basic/            # Fundamental lemmas (bool, option, etc.)
└── README.md             # This file
```

## What Are Universal Lemmas?

Universal lemmas are proven properties that apply across all Move verification projects:
- **Arithmetic**: Commutativity, associativity, identities
- **Monotonicity**: Properties preserved under operations
- **Bitwise**: AND, OR, XOR, shift operations
- **ProgramState**: Monad laws and properties
- **Basic**: Boolean logic, Option type, fundamental types

## How to Use

### 1. Adding Lemmas to the Library

**New Method (Import from Lean files):**

```bash
# Import all lemmas from a Lean file
cargo run --bin lemma_manager -- import lemmas/UInt128/uint128_comparison.lean \
  --module "Universal/UInt128" \
  --category comparison

# Or import all .lean files from a directory
cargo run --bin lemma_manager -- import lemmas/UInt128/ \
  --module "Universal/UInt128" \
  --category comparison

# Skip lake verification (not recommended)
cargo run --bin lemma_manager -- import path/to/file.lean \
  --module "Universal/..." \
  --category "..." \
  --skip-verification
```

**Important**:
- Lemmas must be fully proven - no `sorry` or `axiom` allowed!
- Files are automatically verified with `lake build` before import
- Existing lemmas with the same name will be updated

### 2. Viewing Available Lemmas

```bash
# List all universal lemmas
cargo run --bin lemma_manager -- list --module "Universal/Arithmetic"

# See lemma details
cargo run --bin lemma_manager -- show "nat_add_comm"

# Check statistics
cargo run --bin lemma_manager -- status
```

### 3. Using Lemmas in Your Project

When you run sui-prover with `--backend lean`, lemmas from `lemmas/Universal/` are automatically:
1. Copied to your project's `output/Lemmas/Universal/` directory
2. Made available for import in your proof files

Example import:
```lean
import Lemmas.Universal.Arithmetic
import Lemmas.Universal.Monotonicity

theorem my_proof : ... := by
  apply nat_add_comm  -- Use universal lemma
  ...
```

## Current Lemma Library

### UInt128 Comparison (15 lemmas)

**Reflexivity & Irreflexivity**
- `uint128_le_refl`: `x ≤ x`
- `uint128_lt_irrefl`: `¬(x < x)`

**Transitivity**
- `uint128_le_trans`: `x ≤ y → y ≤ z → x ≤ z`
- `uint128_lt_trans`: `x < y → y < z → x < z`
- `uint128_lt_le_trans`: `x < y → y ≤ z → x < z`
- `uint128_le_lt_trans`: `x ≤ y → y < z → x < z`

**Conversion & Negation**
- `uint128_lt_to_le`: `x < y → x ≤ y`
- `uint128_not_lt_to_ge`: `¬(x < y) → y ≤ x`
- `uint128_not_le_to_gt`: `¬(x ≤ y) → y < x`

**Decidability**
- `uint128_decide_le_true`: `decide (x ≤ y) = true ↔ x ≤ y`
- `uint128_decide_lt_true`: `decide (x < y) = true ↔ x < y`
- `uint128_decide_le_false`: `decide (x ≤ y) = false ↔ ¬(x ≤ y)`
- `uint128_decide_lt_false`: `decide (x < y) = false ↔ ¬(x < y)`

**Special Cases**
- `uint128_zero_le`: `0 ≤ x`
- `uint128_lt_size`: `x < y → x.val < UInt128.size`

## Guidelines for Contributing Lemmas

### What Makes a Good Universal Lemma?

✅ **Good candidates:**
- Fundamental mathematical properties (commutativity, associativity)
- Type-level properties that hold universally (Option, Bool)
- Monad laws
- Basic inequalities and orderings
- Simple, general-purpose facts

❌ **Not universal:**
- Domain-specific properties (e.g., DeFi calculations)
- Function-specific lemmas (belongs in project lemmas)
- Complex proofs requiring deep theory

### Proof Requirements

1. **Must be fully proven** - no `sorry` or `axiom`
2. **Use simple tactics** when possible: `omega`, `rfl`, `decide`, `cases`, `simp`
3. **Keep proofs short** - if it's long, it might not be "universal"
4. **Document dependencies** - use `--dependencies` flag if needed

### Naming Conventions

- Use descriptive names: `nat_add_comm` not `lemma1`
- Follow pattern: `<type>_<operation>_<property>`
- Examples:
  - `nat_add_comm` (Nat addition commutativity)
  - `uint_and_assoc` (UInt AND associativity)
  - `option_map_some` (Option map on Some)

## File Organization

Lemmas are stored in two places:

1. **Source of truth**: `~/.sui-prover/lemma-cache/` (JSON format)
2. **Exported Lean files**: `lemmas/Universal/<Category>/*.lean`

When you add a lemma, it's:
- Saved to cache
- Exported to `lemmas/Universal/<Category>/`
- Committed to version control
- Available for all projects

## Workflow

### Adding a New Lemma

```bash
# 1. Write your lemma in a .lean file
# lemmas/UInt128/my_lemmas.lean:
# theorem uint128_add_comm (x y : UInt128) : x + y = y + x := by
#   show x.val + y.val = y.val + x.val
#   exact Nat.add_comm _ _

# 2. Import to cache (automatically verifies with lake)
cargo run --bin lemma_manager -- import lemmas/UInt128/my_lemmas.lean \
  --module "Universal/UInt128" \
  --category arithmetic

# 3. Verify it was added
cargo run --bin lemma_manager -- status

# 4. Commit to git
git add lemmas/UInt128/my_lemmas.lean
git commit -m "Add UInt128 addition commutativity lemma"
```

### Using in Your Project

The lemmas are automatically available when running sui-prover:

```bash
cd my_move_project/
cargo run --bin sui-prover -- --backend lean

# Lemmas are now in: my_move_project/output/Lemmas/Universal/
```

## Validation

All lemmas are validated before being stored:

```bash
# This will be rejected ❌
cargo run --bin lemma_manager -- add ... --proof "sorry"
# Error: Proof cannot contain 'sorry'

# This will be rejected ❌
cargo run --bin lemma_manager -- add ... --proof "axiom"
# Error: Proof cannot contain 'axiom'

# This will be accepted ✅
cargo run --bin lemma_manager -- add ... --proof "omega"
# Added lemma: ...
```

## Statistics

Run `cargo run --bin lemma_manager -- status` to see:

- Total number of lemmas
- Breakdown by category
- Proven vs. candidate lemmas
- Project hash (for cache invalidation)

## Advanced Usage

### Exporting to Custom Location

```bash
cargo run --bin lemma_manager -- export all --output ./my-custom-path
```

### Filtering Lemmas

```bash
# By module
cargo run --bin lemma_manager -- list --module "Universal/Arithmetic"

# By status
cargo run --bin lemma_manager -- list --status proven
```

### Removing Lemmas

```bash
cargo run --bin lemma_manager -- remove "lemma_id"
```

### Updating Proofs

```bash
# Mark a candidate as proven
cargo run --bin lemma_manager -- mark-proven "lemma_id" "omega"
```

## Contributing

When contributing lemmas to this library:

1. **Check if it already exists**: `cargo run --bin lemma_manager -- list`
2. **Ensure it's universal**: Does it apply to all projects?
3. **Provide a complete proof**: No `sorry` or `axiom`
4. **Use simple tactics**: Keep it maintainable
5. **Add good documentation**: Clear statement, category
6. **Export and commit**: Include generated Lean files

## Future Enhancements

- Automatic lemma discovery from failed proofs
- AI-assisted lemma generation
- Lemma search by pattern
- Dependency visualization
- Cross-project lemma analytics

## Questions?

See the main documentation:
- **Full Guide**: `LEMMA_MANAGER_GUIDE.md` (project root)
- **Implementation**: `IMPLEMENTATION_SUMMARY.md` (project root)
- **Roadmap**: `ACTION_PLAN.md` (project root)
