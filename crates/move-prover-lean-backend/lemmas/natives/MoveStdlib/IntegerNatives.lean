-- Native implementations for std::integer::Integer
-- This is a spec-only type representing mathematical integers

import Prelude.BoundedNat

namespace Integer

-- Integer is represented as Lean's Int (arbitrary precision signed integer)
abbrev Integer := Int

-- Construction from unsigned integers
def from_u8 (x : BoundedNat (2^8)) : Integer := x.val
def from_u16 (x : BoundedNat (2^16)) : Integer := x.val
def from_u32 (x : BoundedNat (2^32)) : Integer := x.val
def from_u64 (x : BoundedNat (2^64)) : Integer := x.val
def from_u128 (x : BoundedNat (2^128)) : Integer := x.val
def from_u256 (x : BoundedNat (2^256)) : Integer := x.val

-- Conversion to unsigned integers
def to_u8 (x : Integer) : BoundedNat (2^8) := ⟨x.toNat % 2^8, Nat.mod_lt _ (by decide)⟩
def to_u16 (x : Integer) : BoundedNat (2^16) := ⟨x.toNat % 2^16, Nat.mod_lt _ (by decide)⟩
def to_u32 (x : Integer) : BoundedNat (2^32) := ⟨x.toNat % 2^32, Nat.mod_lt _ (by decide)⟩
def to_u64 (x : Integer) : BoundedNat (2^64) := ⟨x.toNat % 2^64, Nat.mod_lt _ (by decide)⟩
def to_u128 (x : Integer) : BoundedNat (2^128) := ⟨x.toNat % 2^128, Nat.mod_lt _ (by decide)⟩
def to_u256 (x : Integer) : BoundedNat (2^256) := ⟨x.toNat % 2^256, Nat.mod_lt _ (by decide)⟩

-- Arithmetic operations
def add (x y : Integer) : Integer := x + y
def sub (x y : Integer) : Integer := x - y
def mul (x y : Integer) : Integer := x * y
def div (x y : Integer) : Integer := x / y
def mod (x y : Integer) : Integer := x % y
def neg (x : Integer) : Integer := -x
def sqrt (_x : Integer) : Integer := sorry -- TODO: implement integer square root
def pow (base exp : Integer) : Integer := base ^ exp.toNat

-- Bitwise operations
def bit_or (x y : Integer) : Integer := x.toNat ||| y.toNat
def bit_and (x y : Integer) : Integer := x.toNat &&& y.toNat
def bit_xor (x y : Integer) : Integer := x.toNat ^^^ y.toNat
def bit_not (x : Integer) : Integer := ~~~x.toNat

-- Comparison operations
def lt (x y : Integer) : Bool := x < y
def le (x y : Integer) : Bool := x ≤ y
def lte (x y : Integer) : Bool := x ≤ y
def gt (x y : Integer) : Bool := x > y
def ge (x y : Integer) : Bool := x ≥ y
def gte (x y : Integer) : Bool := x ≥ y

-- Derived functions
def is_neg (x : Integer) : Bool := x < 0
def is_pos (x : Integer) : Bool := x ≥ 0
def abs (x : Integer) : Integer := if x < 0 then -x else x

def div_round_up (x y : Integer) : Integer :=
  let result := x / y
  if x % y != 0 then result + 1 else result

def div_trunc (x y : Integer) : Integer :=
  let result_abs := (abs x) / (abs y)
  if (is_pos x && is_pos y) || (is_neg x && is_neg y) then
    result_abs
  else
    -result_abs

def mod_trunc (x y : Integer) : Integer :=
  x - y * (div_trunc x y)

def shl (x y : Integer) : Integer := x * (pow 2 y)
def shr (x y : Integer) : Integer := x / (pow 2 y)

-- Signed integer conversions
def signed_from_u8 (x : BoundedNat (2^8)) : Integer :=
  if x.val ≤ 0x7f then from_u8 x
  else from_u8 x - from_u8 ⟨0xff, by decide⟩ - 1

def signed_from_u16 (x : BoundedNat (2^16)) : Integer :=
  if x.val ≤ 0x7fff then from_u16 x
  else from_u16 x - from_u16 ⟨0xffff, by decide⟩ - 1

def signed_from_u32 (x : BoundedNat (2^32)) : Integer :=
  if x.val ≤ 0x7fffffff then from_u32 x
  else from_u32 x - from_u32 ⟨0xffffffff, by decide⟩ - 1

def signed_from_u64 (x : BoundedNat (2^64)) : Integer :=
  if x.val ≤ 0x7fffffffffffffff then from_u64 x
  else from_u64 x - from_u64 ⟨0xffffffffffffffff, by decide⟩ - 1

def signed_from_u128 (x : BoundedNat (2^128)) : Integer :=
  if x.val ≤ 0x7fffffffffffffffffffffffffffffff then from_u128 x
  else from_u128 x - from_u128 ⟨0xffffffffffffffffffffffffffffffff, by decide⟩ - 1

def signed_from_u256 (x : BoundedNat (2^256)) : Integer :=
  if x.val ≤ 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff then from_u256 x
  else from_u256 x - from_u256 ⟨0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, by decide⟩ - 1

-- Range checks for signed integers
def is_i8 (x : Integer) : Bool := x ≥ -128 && x ≤ 127
def is_i16 (x : Integer) : Bool := x ≥ -32768 && x ≤ 32767
def is_i32 (x : Integer) : Bool := x ≥ -2147483648 && x ≤ 2147483647
def is_i64 (x : Integer) : Bool := x ≥ -9223372036854775808 && x ≤ 9223372036854775807
def is_i128 (x : Integer) : Bool := x ≥ -170141183460469231731687303715884105728 && x ≤ 170141183460469231731687303715884105727
def is_i256 (x : Integer) : Bool := x ≥ -57896044618658097711785492504343953926634992332820282019728792003956564819968 && x ≤ 57896044618658097711785492504343953926634992332820282019728792003956564819967

-- Abort predicates (these functions are pure and don't abort)
def div_round_up.aborts (_x _y : Integer) : Prop := False
def div_trunc.aborts (_x _y : Integer) : Prop := False
def mod_trunc.aborts (_x _y : Integer) : Prop := False

end Integer
