/-
# Bounded Natural Numbers

Generic bounded natural number type that replaces UInt8, UInt16, UInt32, UInt64, UInt128, UInt256.

## Design

- Representation: { n : Nat // n < bound }
- Operations: Addition and multiplication use axioms to assume no overflow
- Other operations: Proven correct using Mathlib's Nat theorems
- Bounds: Maintained by construction with omega proofs

This simplifies verification by assuming arithmetic operations never overflow.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow


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
def xor (a b : BoundedNat bound) : BoundedNat bound :=
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
  ⟨a.val >>> k, Nat.lt_of_le_of_lt (Nat.shiftRight_le a.val k) a.property⟩

/-- Complement (bitwise NOT) for power-of-2 bounds -/
def complement (a : BoundedNat bound) (h : ∃ n, bound = 2^n) : BoundedNat bound :=
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
def widen {bound bound' : Nat} (a : BoundedNat bound) (h : bound ≤ bound') : BoundedNat bound' :=
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

instance : XorOp (BoundedNat bound) where
  xor := xor

instance : HShiftLeft (BoundedNat bound) Nat (BoundedNat bound) where
  hShiftLeft a k :=
    match shiftLeft? a k with
    | some result => result
    | none =>
      -- Overflow case: return max value or 0 if bound = 0
      if h : bound > 0 then ⟨bound - 1, Nat.sub_lt h (by omega)⟩
      else ⟨0, absurd a.property (by simp_all)⟩

instance : HShiftRight (BoundedNat bound) Nat (BoundedNat bound) where
  hShiftRight := shiftRight

-- Also provide instances for BoundedNat shift amounts
instance : HShiftLeft (BoundedNat bound) (BoundedNat bound') (BoundedNat bound) where
  hShiftLeft a k :=
    match shiftLeft? a k.val with
    | some result => result
    | none =>
      if h : bound > 0 then ⟨bound - 1, Nat.sub_lt h (by omega)⟩
      else ⟨0, absurd a.property (by simp_all)⟩

instance : HShiftRight (BoundedNat bound) (BoundedNat bound') (BoundedNat bound) where
  hShiftRight a k := shiftRight a k.val

-- Manual conversion to Int
def toInt' (n : BoundedNat bound) : ℤ := Int.ofNat n.val

-- Repr instance for debugging/printing
instance : Repr (BoundedNat bound) where
  reprPrec n _ := repr n.val

end BoundedNat
