import Prelude.UInt256
import Prelude.UInt128

-- Shift instances for standard UInt types with Nat shift amounts
instance : HShiftLeft UInt8 Nat UInt8 := ⟨fun a b => a <<< b.toUInt8⟩
instance : HShiftRight UInt8 Nat UInt8 := ⟨fun a b => a >>> b.toUInt8⟩
instance : HShiftLeft UInt16 Nat UInt16 := ⟨fun a b => a <<< b.toUInt16⟩
instance : HShiftRight UInt16 Nat UInt16 := ⟨fun a b => a >>> b.toUInt16⟩
instance : HShiftLeft UInt32 Nat UInt32 := ⟨fun a b => a <<< b.toUInt32⟩
instance : HShiftRight UInt32 Nat UInt32 := ⟨fun a b => a >>> b.toUInt32⟩
instance : HShiftLeft UInt64 Nat UInt64 := ⟨fun a b => a <<< b.toUInt64⟩
instance : HShiftRight UInt64 Nat UInt64 := ⟨fun a b => a >>> b.toUInt64⟩

def is_equal_Bool (a : Bool) (b : Bool) : Bool :=
    match a, b with
    | true, true => true
    | false, false => true
    | _, _ => false

def is_valid_Bool (_ : Bool) : Bool :=
    true

def is_equal_u8 (a : UInt8) (b : UInt8) : Bool :=
    a == b

def is_valid_u8 (_ : UInt8) : Bool :=
    true

def is_equal_u16 (a : UInt16) (b : UInt16) : Bool :=
    a == b

def is_valid_u16 (_ : UInt16) : Bool :=
    true

def is_equal_u32 (a : UInt32) (b : UInt32) : Bool :=
    a == b

def is_valid_u32 (_ : UInt32) : Bool :=
    true

def is_equal_u64 (a : UInt64) (b : UInt64) : Bool :=
    a == b

def is_valid_u64 (_ : UInt64) : Bool :=
    true

def is_equal_u128 (a : UInt128) (b : UInt128) : Bool :=
    a == b

def is_valid_u128 (_ : UInt128) : Bool :=
    true

def is_equal_u256 (a : UInt256) (b : UInt256) : Bool :=
    a == b

def is_valid_u256 (_ : UInt256) : Bool :=
    true

-- Vec type (used for Move vector)
def Vec (α : Type) : Type := List α

-- BEq instance for Vec (required for is_equal_vec)
instance [BEq α] : BEq (Vec α) := inferInstanceAs (BEq (List α))

-- Heterogeneous OR instances for mixed-size integer operations
instance : HOr UInt128 UInt8 UInt128 where
  hOr a b := a ||| UInt128.ofNat b.toNat

instance : HOr UInt256 UInt8 UInt256 where
  hOr a b := a ||| UInt256.ofNat b.toNat

instance : HOr UInt256 UInt128 UInt256 where
  hOr a b := a ||| UInt256.ofNat b.toNat

def is_valid_vec (α : Type) [BEq α] (_ : Vec α) : Bool :=
    true  -- All Vecs are valid by construction

def is_equal_vec (α : Type) [BEq α] (v1 v2 : Vec α) : Bool :=
    v1 == v2

-- Special case for Bool since type parameter syntax is tricky
def is_valid_vec'Bool' (v : Vec Bool) : Bool :=
    is_valid_vec Bool v

def is_equal_vec'Bool' (v1 v2 : Vec Bool) : Bool :=
    is_equal_vec Bool v1 v2

-- Address type (used for Move address)
structure Address where
    bytes : UInt256
    deriving BEq, Repr

def is_valid_address (_ : Address) : Bool :=
    true  -- All addresses are valid by construction

def is_equal_address (addr1 addr2 : Address) : Bool :=
    addr1 == addr2
