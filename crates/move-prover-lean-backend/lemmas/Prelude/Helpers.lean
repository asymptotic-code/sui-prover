import Prelude.BoundedNat

-- ============================================================================
-- Homogeneous bitwise operator instances for all UInt types
-- Following Move semantics: bitwise operations require same-type operands
-- ============================================================================

instance : AndOp UInt8 := ⟨fun a b => UInt8.land a b⟩
instance : OrOp UInt8 := ⟨fun a b => UInt8.lor a b⟩
instance : XorOp UInt8 := ⟨fun a b => UInt8.xor a b⟩
instance : HShiftLeft UInt8 UInt8 UInt8 := ⟨fun a b => UInt8.shiftLeft a b⟩
instance : HShiftRight UInt8 UInt8 UInt8 := ⟨fun a b => UInt8.shiftRight a b⟩

instance : AndOp UInt16 := ⟨fun a b => UInt16.land a b⟩
instance : OrOp UInt16 := ⟨fun a b => UInt16.lor a b⟩
instance : XorOp UInt16 := ⟨fun a b => UInt16.xor a b⟩
instance : HShiftLeft UInt16 UInt8 UInt16 := ⟨fun a b => UInt16.shiftLeft a b.toUInt16⟩
instance : HShiftRight UInt16 UInt8 UInt16 := ⟨fun a b => UInt16.shiftRight a b.toUInt16⟩

instance : AndOp UInt32 := ⟨fun a b => UInt32.land a b⟩
instance : OrOp UInt32 := ⟨fun a b => UInt32.lor a b⟩
instance : XorOp UInt32 := ⟨fun a b => UInt32.xor a b⟩
instance : HShiftLeft UInt32 UInt8 UInt32 := ⟨fun a b => UInt32.shiftLeft a b.toUInt32⟩
instance : HShiftRight UInt32 UInt8 UInt32 := ⟨fun a b => UInt32.shiftRight a b.toUInt32⟩

instance : AndOp UInt64 := ⟨fun a b => UInt64.land a b⟩
instance : OrOp UInt64 := ⟨fun a b => UInt64.lor a b⟩
instance : XorOp UInt64 := ⟨fun a b => UInt64.xor a b⟩
instance : HShiftLeft UInt64 UInt8 UInt64 := ⟨fun a b => UInt64.shiftLeft a b.toUInt64⟩
instance : HShiftRight UInt64 UInt8 UInt64 := ⟨fun a b => UInt64.shiftRight a b.toUInt64⟩

-- Vec type (used for Move vector)
def Vec (α : Type) : Type := List α

-- BEq instance for Vec (required for is_equal_vec)
instance [BEq α] : BEq (Vec α) := inferInstanceAs (BEq (List α))

-- Address type (used for Move address)
structure Address where
    bytes : BoundedNat (2^256)
    deriving BEq, Repr
