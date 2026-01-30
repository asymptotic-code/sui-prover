import Prelude.BoundedNat

-- Type conversion helpers for unsigned integer types
-- For BoundedNat types, we use the generic convert function

-- Bool conversions
namespace Bool
def toBoundedNat (bound : Nat) (b : Bool) : BoundedNat bound :=
  if h : bound > 1 then
    if b then ⟨1, by omega⟩ else ⟨0, by omega⟩
  else if h0 : bound > 0 then
    ⟨0, h0⟩
  else
    ⟨0, BoundedNat_bound_zero_absurd (by omega)⟩
end Bool

-- UInt8 conversions (including identity for uniformity)
namespace UInt8
def toUInt8' (a : UInt8) : UInt8 := a
def toBoundedNat (bound : Nat) (a : UInt8) : BoundedNat bound :=
  BoundedNat.convert ⟨a.toNat, UInt8.toNat_lt a⟩
end UInt8

-- UInt16 conversions (including identity for uniformity)
namespace UInt16
def toUInt16' (a : UInt16) : UInt16 := a
def toBoundedNat (bound : Nat) (a : UInt16) : BoundedNat bound :=
  BoundedNat.convert ⟨a.toNat, UInt16.toNat_lt a⟩
end UInt16

-- UInt32 conversions (including identity for uniformity)
namespace UInt32
def toUInt32' (a : UInt32) : UInt32 := a
def toBoundedNat (bound : Nat) (a : UInt32) : BoundedNat bound :=
  BoundedNat.convert ⟨a.toNat, UInt32.toNat_lt a⟩
end UInt32

-- UInt64 conversions (including identity for uniformity)
namespace UInt64
def toUInt64' (a : UInt64) : UInt64 := a
def toBoundedNat (bound : Nat) (a : UInt64) : BoundedNat bound :=
  BoundedNat.convert ⟨a.toNat, UInt64.toNat_lt a⟩
end UInt64

-- BoundedNat conversions to standard UInt types
namespace BoundedNat
def toUInt8' {bound : Nat} (a : BoundedNat bound) : UInt8 := UInt8.ofNat a.val
def toUInt16' {bound : Nat} (a : BoundedNat bound) : UInt16 := UInt16.ofNat a.val
def toUInt32' {bound : Nat} (a : BoundedNat bound) : UInt32 := UInt32.ofNat a.val
def toUInt64' {bound : Nat} (a : BoundedNat bound) : UInt64 := UInt64.ofNat a.val
end BoundedNat
