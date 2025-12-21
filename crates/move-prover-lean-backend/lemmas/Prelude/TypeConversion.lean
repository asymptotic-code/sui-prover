import Prelude.BoundedNat

-- Type conversion helpers for unsigned integer types
-- Using BoundedNat for u128 and u256 types

-- Type aliases for convenience
abbrev U128 := BoundedNat (2^128)
abbrev U256 := BoundedNat (2^256)

-- Bool conversions to BoundedNat types
namespace Bool
def toU128 (b : Bool) : U128 := if b then ⟨1, by native_decide⟩ else ⟨0, by native_decide⟩
def toU256 (b : Bool) : U256 := if b then ⟨1, by native_decide⟩ else ⟨0, by native_decide⟩
end Bool

-- UInt8 conversions (including identity for uniformity)
namespace UInt8
def toU128 (a : UInt8) : U128 :=
  ⟨a.toNat, Nat.lt_of_lt_of_le a.toFin.isLt (by native_decide : 2^8 ≤ 2^128)⟩
def toU256 (a : UInt8) : U256 :=
  ⟨a.toNat, Nat.lt_of_lt_of_le a.toFin.isLt (by native_decide : 2^8 ≤ 2^256)⟩
end UInt8

-- UInt16 conversions
namespace UInt16
def toU128 (a : UInt16) : U128 :=
  ⟨a.toNat, Nat.lt_of_lt_of_le a.toFin.isLt (by native_decide : 2^16 ≤ 2^128)⟩
def toU256 (a : UInt16) : U256 :=
  ⟨a.toNat, Nat.lt_of_lt_of_le a.toFin.isLt (by native_decide : 2^16 ≤ 2^256)⟩
end UInt16

-- UInt32 conversions
namespace UInt32
def toU128 (a : UInt32) : U128 :=
  ⟨a.toNat, Nat.lt_of_lt_of_le a.toFin.isLt (by native_decide : 2^32 ≤ 2^128)⟩
def toU256 (a : UInt32) : U256 :=
  ⟨a.toNat, Nat.lt_of_lt_of_le a.toFin.isLt (by native_decide : 2^32 ≤ 2^256)⟩
end UInt32

-- UInt64 conversions
namespace UInt64
def toU128 (a : UInt64) : U128 :=
  ⟨a.toNat, Nat.lt_of_lt_of_le a.toFin.isLt (by native_decide : 2^64 ≤ 2^128)⟩
def toU256 (a : UInt64) : U256 :=
  ⟨a.toNat, Nat.lt_of_lt_of_le a.toFin.isLt (by native_decide : 2^64 ≤ 2^256)⟩
end UInt64

-- BoundedNat conversions to standard types
namespace BoundedNat
def toUInt8 (a : BoundedNat n) : UInt8 := UInt8.ofNat a.val
def toUInt16 (a : BoundedNat n) : UInt16 := UInt16.ofNat a.val
def toUInt32 (a : BoundedNat n) : UInt32 := UInt32.ofNat a.val
def toUInt64 (a : BoundedNat n) : UInt64 := UInt64.ofNat a.val
end BoundedNat
