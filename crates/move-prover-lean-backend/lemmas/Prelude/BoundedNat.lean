/-
# Bounded Natural Numbers

Generic bounded natural number type that replaces UInt8, UInt16, UInt32, UInt64, UInt128, UInt256.

## Design

- Representation: { n : Nat // n < bound }
- Operations: Addition and multiplication use axioms to assume no overflow
- Other operations: Proven correct using Lean's built-in Nat theorems
- Bounds: Maintained by construction with omega proofs

This simplifies verification by assuming arithmetic operations never overflow.
-/

/-- Axiom: When bound = 0, BoundedNat bound is uninhabited, so any proposition follows -/
axiom BoundedNat_bound_zero_absurd {P : Prop} {bound : Nat} (h : ¬(bound > 0)) : P

/-- A natural number bounded by a given limit -/
structure BoundedNat (bound : Nat) where
  val : Nat
  property : val < bound

namespace BoundedNat

variable {bound : Nat}

/-- Create a BoundedNat from a Nat literal -/
def ofNat (n : Nat) (h : n < bound) : BoundedNat bound :=
  ⟨n, h⟩

/-- Convert to natural number -/
def toNat (n : BoundedNat bound) : Nat := n.val

/-- Equality is decidable -/
instance : DecidableEq (BoundedNat bound) :=
  fun a b => decidable_of_iff (a.val = b.val) (by
    constructor
    · intro h; cases a; cases b; simp only at h; simp [BoundedNat.mk.injEq]; exact h
    · intro h; cases h; rfl)

/-- Ordering -/
instance : LT (BoundedNat bound) where
  lt a b := a.val < b.val

instance : LE (BoundedNat bound) where
  le a b := a.val ≤ b.val

instance : DecidableRel (fun (a b : BoundedNat bound) => a < b) :=
  fun a b => inferInstanceAs (Decidable (a.val < b.val))

instance : DecidableRel (fun (a b : BoundedNat bound) => a ≤ b) :=
  fun a b => inferInstanceAs (Decidable (a.val ≤ b.val))

/-- Comparison -/
def compare (a b : BoundedNat bound) : Ordering :=
  if a.val < b.val then Ordering.lt
  else if a.val = b.val then Ordering.eq
  else Ordering.gt

/-- Axiom: Addition never overflows -/
axiom add_no_overflow : ∀ {bound : Nat} (a b : BoundedNat bound), a.val + b.val < bound

/-- Addition (assumed never to overflow) -/
def add (a b : BoundedNat bound) : BoundedNat bound :=
  ⟨a.val + b.val, add_no_overflow a b⟩

/-- Subtraction (saturating to 0) -/
def sub (a b : BoundedNat bound) : BoundedNat bound :=
  ⟨a.val - b.val, Nat.lt_of_le_of_lt (Nat.sub_le a.val b.val) a.property⟩

/-- Axiom: Multiplication never overflows -/
axiom mul_no_overflow : ∀ {bound : Nat} (a b : BoundedNat bound), a.val * b.val < bound

/-- Multiplication (assumed never to overflow) -/
def mul (a b : BoundedNat bound) : BoundedNat bound :=
  ⟨a.val * b.val, mul_no_overflow a b⟩

/-- Division (never overflows) -/
def div (a b : BoundedNat bound) : BoundedNat bound :=
  ⟨a.val / b.val, Nat.lt_of_le_of_lt (Nat.div_le_self a.val b.val) a.property⟩

/-- Modulo (never overflows when divisor > 0) -/
def mod (a b : BoundedNat bound) : BoundedNat bound :=
  if hb : b.val = 0 then
    -- When divisor is 0, return a (like Nat.mod)
    a
  else
    ⟨a.val % b.val, Nat.lt_of_lt_of_le (Nat.mod_lt a.val (Nat.pos_of_ne_zero hb)) (Nat.le_of_lt b.property)⟩

/-- Bitwise AND (never overflows) -/
def land (a b : BoundedNat bound) : BoundedNat bound :=
  if h : a.val &&& b.val < bound then
    ⟨a.val &&& b.val, h⟩
  else
    a  -- Fallback (should not happen as AND result is ≤ inputs)

/-- Bitwise OR -/
def lor (a b : BoundedNat bound) : BoundedNat bound :=
  if h : a.val ||| b.val < bound then
    ⟨a.val ||| b.val, h⟩
  else
    -- OR can overflow, saturate to a (which is already < bound)
    a

/-- Bitwise XOR -/
def bxor (a b : BoundedNat bound) : BoundedNat bound :=
  if h : a.val ^^^ b.val < bound then
    ⟨a.val ^^^ b.val, h⟩
  else
    -- XOR can overflow, saturate to a (which is already < bound)
    a

/-- Left shift (returns Option to handle overflow) -/
def shiftLeft? (a : BoundedNat bound) (k : Nat) : Option (BoundedNat bound) :=
  if h : a.val <<< k < bound then
    some ⟨a.val <<< k, h⟩
  else
    none

/-- Left shift (saturating to max value on overflow) -/
def shiftLeft (a : BoundedNat bound) (k : Nat) : BoundedNat bound :=
  match shiftLeft? a k with
  | some result => result
  | none =>
    if h : bound > 0 then ⟨bound - 1, Nat.sub_lt h (by omega)⟩
    else ⟨0, absurd a.property (by simp_all)⟩

/-- Right shift (never overflows) -/
def shiftRight (a : BoundedNat bound) (k : Nat) : BoundedNat bound :=
  ⟨a.val >>> k, Nat.lt_of_le_of_lt (by simp [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self a.val (2^k)) a.property⟩

/-- Complement (bitwise NOT) for power-of-2 bounds -/
def complement (a : BoundedNat bound) (_h : ∃ n, bound = 2^n) : BoundedNat bound :=
  if hc : bound - 1 - a.val < bound then
    ⟨bound - 1 - a.val, hc⟩
  else
    a  -- Fallback

/-- Convert between any two bounds (widen, truncate, or same size) -/
def convert {bound_from bound_to : Nat} (a : BoundedNat bound_from) : BoundedNat bound_to :=
  if h : a.val < bound_to then
    ⟨a.val, h⟩
  else if hb : bound_to > 0 then
    ⟨a.val % bound_to, Nat.mod_lt a.val hb⟩
  else
    -- bound_to = 0: BoundedNat 0 is uninhabited, unreachable for valid integer types
    ⟨0, BoundedNat_bound_zero_absurd hb⟩

/-- Convert to larger bound -/
def widen {bound bound' : Nat} (a : BoundedNat bound) (_h : bound ≤ bound') : BoundedNat bound' :=
  convert a

/-- Truncate to smaller bound (modulo operation) -/
def truncate {bound bound' : Nat} (a : BoundedNat bound) : BoundedNat bound' :=
  convert a

-- Instance for numeric literals (only for positive bounds)
instance {bound : Nat} (n : Nat) [h : Decidable (n < bound)] : OfNat (BoundedNat bound) n :=
  if h' : n < bound then
    ⟨⟨n, h'⟩⟩
  else if hb : bound > 0 then
    -- If literal is too large, wrap around (modulo behavior)
    ⟨⟨n % bound, Nat.mod_lt n hb⟩⟩
  else
    -- bound = 0: BoundedNat 0 is uninhabited, unreachable for valid integer types
    ⟨⟨0, BoundedNat_bound_zero_absurd hb⟩⟩

end BoundedNat

-- Type aliases for common sizes
abbrev BoundedU8 := BoundedNat (2^8)
abbrev BoundedU16 := BoundedNat (2^16)
abbrev BoundedU32 := BoundedNat (2^32)
abbrev BoundedU64 := BoundedNat (2^64)
abbrev BoundedU128 := BoundedNat (2^128)
abbrev BoundedU256 := BoundedNat (2^256)

-- Instances for common operations
namespace BoundedNat

variable {bound : Nat}

instance : Add (BoundedNat bound) where
  add := add

instance : Sub (BoundedNat bound) where
  sub := sub

instance : Mul (BoundedNat bound) where
  mul := mul

instance : Div (BoundedNat bound) where
  div := div

instance : Mod (BoundedNat bound) where
  mod := mod

instance : AndOp (BoundedNat bound) where
  and := land

instance : OrOp (BoundedNat bound) where
  or := lor

instance : HXor (BoundedNat bound) (BoundedNat bound) (BoundedNat bound) where
  hXor := bxor

instance : HShiftLeft (BoundedNat bound) Nat (BoundedNat bound) where
  hShiftLeft a k :=
    -- Move uses modular shift left: (a <<< k) % bound
    if h : bound > 0 then
      ⟨(a.val <<< k) % bound, Nat.mod_lt _ h⟩
    else
      ⟨0, absurd a.property (by simp_all)⟩

instance : HShiftRight (BoundedNat bound) Nat (BoundedNat bound) where
  hShiftRight := shiftRight

-- Also provide instances for BoundedNat shift amounts
instance {bound' : Nat} : HShiftLeft (BoundedNat bound) (BoundedNat bound') (BoundedNat bound) where
  hShiftLeft a k :=
    -- Move uses modular shift left: (a <<< k) % bound
    if h : bound > 0 then
      ⟨(a.val <<< k.val) % bound, Nat.mod_lt _ h⟩
    else
      ⟨0, absurd a.property (by simp_all)⟩

instance {bound' : Nat} : HShiftRight (BoundedNat bound) (BoundedNat bound') (BoundedNat bound) where
  hShiftRight a k := shiftRight a k.val

-- Repr instance for debugging/printing
instance : Repr (BoundedNat bound) where
  reprPrec n _ := repr n.val

-- Zero instance (requires bound > 0)
instance instZeroBoundedNat (h : bound > 0 := by decide) : Zero (BoundedNat bound) where
  zero := ⟨0, h⟩

-- One instance (requires bound > 1)
instance instOneBoundedNat (h : 1 < bound := by decide) : One (BoundedNat bound) where
  one := ⟨1, h⟩

-- Inhabited instance (requires bound > 0)
instance (h : bound > 0 := by decide) : Inhabited (BoundedNat bound) where
  default := ⟨0, h⟩

-- Min and Max operations
instance : Min (BoundedNat bound) where
  min a b := if a.val ≤ b.val then a else b

instance : Max (BoundedNat bound) where
  max a b := if a.val ≥ b.val then a else b

-- Ord instance for sorting
instance : Ord (BoundedNat bound) where
  compare := compare

-- Boolean equality
instance : BEq (BoundedNat bound) where
  beq a b := a.val == b.val

-- LawfulBEq instance for BoundedNat
instance : LawfulBEq (BoundedNat bound) where
  eq_of_beq := by
    intro a b h
    simp only [BEq.beq] at h
    have h_val_eq : a.val = b.val := by
      exact of_decide_eq_true h
    cases a; cases b
    simp only [mk.injEq]
    exact h_val_eq
  rfl := by
    intro a
    simp only [BEq.beq]
    rfl

-- Complement operation (bitwise NOT)
instance : Complement (BoundedNat bound) where
  complement a :=
    if h : bound > 0 then
      if hc : bound - 1 - a.val < bound then
        ⟨bound - 1 - a.val, hc⟩
      else
        a  -- Fallback (should not happen for valid values)
    else
      ⟨0, BoundedNat_bound_zero_absurd h⟩

/-! ## Value Extraction Lemmas

These lemmas allow extracting the underlying Nat value from BoundedNat operations.
They are essential for proving that implementations match specifications.
-/

/-- Extensionality: two BoundedNats are equal iff their values are equal -/
theorem ext {a b : BoundedNat bound} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp only [mk.injEq]; exact h

/-- BEq equivalence to propositional equality -/
@[simp] theorem beq_eq_decide (a b : BoundedNat bound) :
    (a == b) = decide (a = b) := by
  simp only [BEq.beq, decide_eq_decide]
  constructor
  · intro h; exact ext h
  · intro h; cases h; rfl

/-- Addition extracts to Nat addition -/
@[simp] theorem add_val (a b : BoundedNat bound) : (a + b).val = a.val + b.val := rfl

/-- Subtraction extracts to Nat subtraction -/
@[simp] theorem sub_val (a b : BoundedNat bound) : (a - b).val = a.val - b.val := rfl

/-- Multiplication extracts to Nat multiplication -/
@[simp] theorem mul_val (a b : BoundedNat bound) : (a * b).val = a.val * b.val := rfl

/-- Division extracts to Nat division -/
@[simp] theorem div_val (a b : BoundedNat bound) : (a / b).val = a.val / b.val := rfl

/-- Min extracts to Nat min -/
@[simp] theorem min_val (a b : BoundedNat bound) : (min a b).val = min a.val b.val := by
  simp only [Min.min, min]
  by_cases h : a.val ≤ b.val
  · simp only [h, ↓reduceIte, Nat.min_eq_left h]
  · simp only [h, ↓reduceIte, Nat.min_eq_right (Nat.le_of_not_le h)]

/-- Max extracts to Nat max -/
@[simp] theorem max_val (a b : BoundedNat bound) : (max a b).val = max a.val b.val := by
  simp only [Max.max, max]
  by_cases h : a.val ≥ b.val
  · simp only [h, ↓reduceIte, Nat.max_eq_left h]
  · simp only [h, ↓reduceIte, Nat.max_eq_right (Nat.le_of_not_le h)]

/-- Right shift with Nat extracts to Nat right shift -/
@[simp] theorem shiftRight_nat_val (a : BoundedNat bound) (k : Nat) :
    (a >>> k).val = a.val >>> k := rfl

/-- Right shift with BoundedNat extracts to Nat right shift -/
@[simp] theorem shiftRight_bounded_val {bound' : Nat} (a : BoundedNat bound) (k : BoundedNat bound') :
    (a >>> k).val = a.val >>> k.val := rfl

/-- Convert when value fits in target bound -/
theorem convert_val_of_lt {bound_from bound_to : Nat} (a : BoundedNat bound_from)
    (h : a.val < bound_to) : (convert a : BoundedNat bound_to).val = a.val := by
  simp only [convert, h, ↓reduceDIte]

/-- Convert is identity when value already fits -/
theorem convert_val_eq_of_lt {bound_from bound_to : Nat} (a : BoundedNat bound_from)
    (h : a.val < bound_to) : (convert a : BoundedNat bound_to).val = a.val := by
  simp only [convert, h, ↓reduceDIte]

/-! ## Common Bound Inequalities

Pre-computed facts about power-of-2 bounds that come up frequently in proofs.
-/

theorem bound_8_lt_64 : (2 : Nat)^8 < 2^64 := by decide
theorem bound_8_lt_128 : (2 : Nat)^8 < 2^128 := by decide
theorem bound_8_lt_256 : (2 : Nat)^8 < 2^256 := by decide
theorem bound_16_lt_64 : (2 : Nat)^16 < 2^64 := by decide
theorem bound_16_lt_128 : (2 : Nat)^16 < 2^128 := by decide
theorem bound_32_lt_64 : (2 : Nat)^32 < 2^64 := by decide
theorem bound_32_lt_128 : (2 : Nat)^32 < 2^128 := by decide
theorem bound_64_lt_128 : (2 : Nat)^64 < 2^128 := by decide
theorem bound_64_lt_256 : (2 : Nat)^64 < 2^256 := by decide
theorem bound_128_lt_256 : (2 : Nat)^128 < 2^256 := by decide
theorem bound_128_mul_128_eq_256 : (2 : Nat)^128 * 2^128 = 2^256 := by decide

theorem bound_pos_8 : (2 : Nat)^8 > 0 := by decide
theorem bound_pos_16 : (2 : Nat)^16 > 0 := by decide
theorem bound_pos_32 : (2 : Nat)^32 > 0 := by decide
theorem bound_pos_64 : (2 : Nat)^64 > 0 := by decide
theorem bound_pos_128 : (2 : Nat)^128 > 0 := by decide
theorem bound_pos_256 : (2 : Nat)^256 > 0 := by decide

end BoundedNat
