-- Native implementations for prover::real module
-- Provides arithmetic operations using Mathlib's Real type

import Prelude.BoundedNat
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace MoveReal

-- Real type from Mathlib
-- The Move struct Real maps to Mathlib's Real type
abbrev Real := _root_.Real

-- Real operations are noncomputable
noncomputable section

-- ============================================================================
-- Constructors from unsigned integers (using BoundedNat)
-- ============================================================================

def from_u8 (n : BoundedNat (2^8)) : Real := n.val
def from_u16 (n : BoundedNat (2^16)) : Real := n.val
def from_u32 (n : BoundedNat (2^32)) : Real := n.val
def from_u64 (n : BoundedNat (2^64)) : Real := n.val
def from_u128 (n : BoundedNat (2^128)) : Real := n.val
def from_u256 (n : BoundedNat (2^256)) : Real := n.val

-- ============================================================================
-- Constructors from signed integers (two's complement)
-- ============================================================================

def from_i8_bits (bits : BoundedNat (2^8)) : Real :=
  let n := bits.val
  if n < 2^7 then (n : Int) else (n : Int) - 2^8

def from_i16_bits (bits : BoundedNat (2^16)) : Real :=
  let n := bits.val
  if n < 2^15 then (n : Int) else (n : Int) - 2^16

def from_i32_bits (bits : BoundedNat (2^32)) : Real :=
  let n := bits.val
  if n < 2^31 then (n : Int) else (n : Int) - 2^32

def from_i64_bits (bits : BoundedNat (2^64)) : Real :=
  let n := bits.val
  if n < 2^63 then (n : Int) else (n : Int) - 2^64

def from_i128_bits (bits : BoundedNat (2^128)) : Real :=
  let n := bits.val
  if n < 2^127 then (n : Int) else (n : Int) - 2^128

-- ============================================================================
-- Constructor from numerator/denominator
-- ============================================================================

def from_fraction (num : Real) (den : Real) : Real := num / den

-- ============================================================================
-- Basic arithmetic operations
-- ============================================================================

def add (a b : Real) : Real := a + b
def sub (a b : Real) : Real := a - b
def mul (a b : Real) : Real := a * b
def div (a b : Real) : Real := a / b
def neg (a : Real) : Real := -a
def abs (a : Real) : Real := if a < 0 then -a else a

-- ============================================================================
-- Power operations
-- ============================================================================

def pow_nat (base : Real) (exp : Nat) : Real := base ^ exp

def pow_int (base : Real) (exp : Int) : Real :=
  if exp >= 0 then
    base ^ exp.toNat
  else
    1 / (base ^ (-exp).toNat)

def pow (base : Real) (exp : Real) : Real :=
  Real.rpow base exp

-- ============================================================================
-- Rounding operations
-- ============================================================================

def floor (r : Real) : Real := ⌊r⌋
def ceil (r : Real) : Real := ⌈r⌉
def trunc (r : Real) : Real := if r >= 0 then ⌊r⌋ else ⌈r⌉

def round (r : Real) : Real :=
  let half : Real := 1 / 2
  if r >= 0 then floor (r + half) else ceil (r - half)

-- ============================================================================
-- Floor to unsigned integer types (using BoundedNat)
-- ============================================================================

-- Helper to convert floor result to BoundedNat with bounds proof
private def floorToBoundedNat (r : Real) (bound : Nat) (h : bound > 0) : BoundedNat bound :=
  let q := if r >= 0 then Int.toNat ⌊r⌋ else 0
  ⟨q % bound, Nat.mod_lt q h⟩

def floor_u8 (r : Real) : BoundedNat (2^8) :=
  floorToBoundedNat r (2^8) (by decide)

def floor_u16 (r : Real) : BoundedNat (2^16) :=
  floorToBoundedNat r (2^16) (by decide)

def floor_u32 (r : Real) : BoundedNat (2^32) :=
  floorToBoundedNat r (2^32) (by decide)

def floor_u64 (r : Real) : BoundedNat (2^64) :=
  floorToBoundedNat r (2^64) (by decide)

def floor_u128 (r : Real) : BoundedNat (2^128) :=
  floorToBoundedNat r (2^128) (by decide)

def floor_u256 (r : Real) : BoundedNat (2^256) :=
  floorToBoundedNat r (2^256) (by decide)

-- ============================================================================
-- Comparison operations
-- ============================================================================

def eq (a b : Real) : Bool := a == b
def ne (a b : Real) : Bool := a != b
def lt (a b : Real) : Bool := a < b
def le (a b : Real) : Bool := a <= b
def gt (a b : Real) : Bool := a > b
def ge (a b : Real) : Bool := a >= b

-- ============================================================================
-- Min/Max
-- ============================================================================

def min (a b : Real) : Real := if a <= b then a else b
def max (a b : Real) : Real := if a >= b then a else b

-- ============================================================================
-- Accessors
-- ============================================================================

def numerator (r : Real) : Real := r
def denominator (r : Real) : Real := 1

-- ============================================================================
-- Predicates
-- ============================================================================

def is_zero (r : Real) : Bool := r == 0
def is_positive (r : Real) : Bool := r > 0
def is_negative (r : Real) : Bool := r < 0
def is_integer (r : Real) : Bool := r == ⌊r⌋

-- ============================================================================
-- Constants
-- ============================================================================

def zero : Real := 0
def one : Real := 1

-- ============================================================================
-- Square root and logarithm - use Mathlib's definitions
-- ============================================================================

-- Wrapper for Mathlib's sqrt
def sqrt (x : Real) : Real := Real.sqrt x

-- Natural logarithm (wraps Mathlib's Real.log)
def ln (x : Real) : Real := Real.log x

end -- noncomputable section

end MoveReal
