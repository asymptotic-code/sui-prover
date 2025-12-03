import Prelude.UInt256
import Prelude.UInt128

-- Type conversion helpers for unsigned integer types
-- Lean's standard library defines most conversions between UInt8/16/32/64
-- We only need to add conversions to/from our custom UInt128 and UInt256

-- Bool conversions to our custom UInt types
-- (Lean 4 already defines Bool.toUInt8/16/32/64)
namespace Bool
def toUInt128 (b : Bool) : UInt128 := if b then 1 else 0
def toUInt256 (b : Bool) : UInt256 := if b then 1 else 0
end Bool

-- UInt8 conversions (including identity for uniformity)
namespace UInt8
def toUInt8 (a : UInt8) : UInt8 := a
def toUInt128 (a : UInt8) : UInt128 := UInt128.ofNat a.toNat
def toUInt256 (a : UInt8) : UInt256 := UInt256.ofNat a.toNat
end UInt8

-- UInt16 conversions (including identity for uniformity)
namespace UInt16
def toUInt16 (a : UInt16) : UInt16 := a
def toUInt128 (a : UInt16) : UInt128 := UInt128.ofNat a.toNat
def toUInt256 (a : UInt16) : UInt256 := UInt256.ofNat a.toNat
end UInt16

-- UInt32 conversions (including identity for uniformity)
namespace UInt32
def toUInt32 (a : UInt32) : UInt32 := a
def toUInt128 (a : UInt32) : UInt128 := UInt128.ofNat a.toNat
def toUInt256 (a : UInt32) : UInt256 := UInt256.ofNat a.toNat
end UInt32

-- UInt64 conversions (including identity for uniformity)
namespace UInt64
def toUInt64 (a : UInt64) : UInt64 := a
def toUInt128 (a : UInt64) : UInt128 := UInt128.ofNat a.toNat
def toUInt256 (a : UInt64) : UInt256 := UInt256.ofNat a.toNat
end UInt64

-- UInt128 conversions to standard types (including identity)
namespace UInt128
def toUInt8 (a : UInt128) : UInt8 := UInt8.ofNat a.toNat
def toUInt16 (a : UInt128) : UInt16 := UInt16.ofNat a.toNat
def toUInt32 (a : UInt128) : UInt32 := UInt32.ofNat a.toNat
def toUInt64 (a : UInt128) : UInt64 := UInt64.ofNat a.toNat
def toUInt128 (a : UInt128) : UInt128 := a
-- toUInt256 already defined in UInt128.lean
end UInt128

-- UInt256 conversions to standard types (including identity)
namespace UInt256
def toUInt8 (a : UInt256) : UInt8 := UInt8.ofNat a.toNat
def toUInt16 (a : UInt256) : UInt16 := UInt16.ofNat a.toNat
def toUInt32 (a : UInt256) : UInt32 := UInt32.ofNat a.toNat
def toUInt64 (a : UInt256) : UInt64 := UInt64.ofNat a.toNat
def toUInt256 (a : UInt256) : UInt256 := a
-- toUInt128 already defined in UInt128.lean
end UInt256
