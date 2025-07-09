import Init.Data.Nat.Div

/-- The size of type `UInt256`, that is, `2^256`. -/
def UInt256.size : Nat :=
  115792089237316195423570985008687907853269984665640564039457584007913129639936

structure UInt256 where
  val : Fin UInt256.size
  deriving BEq, Ord

instance : ToString UInt256 where
  toString a := toString a.val

namespace UInt256

def ofNat (n : Nat) : UInt256 := ⟨n % UInt256.size, Nat.mod_lt n (by simp [UInt256.size])⟩

def toNat (u : UInt256) : Nat := u.val.val

instance : Repr UInt256 where
  reprPrec n _ := repr n.toNat

instance {n : Nat} : OfNat UInt256 n := ⟨ofNat n⟩
instance {n : Nat} : OfNat (Fin UInt256.size) n := ⟨(ofNat n).val⟩
instance : Inhabited UInt256 := ⟨ofNat 0⟩

end UInt256


abbrev Nat.toUInt256 : Nat → UInt256 := UInt256.ofNat

abbrev Nat.toNat : Nat → Nat := fun n => n

namespace UInt256

def add (a b : UInt256) : UInt256 := ⟨a.val + b.val⟩
def sub (a b : UInt256) : UInt256 := ⟨a.val - b.val⟩
def mul (a b : UInt256) : UInt256 := ⟨a.val * b.val⟩
def div (a b : UInt256) : UInt256 := ⟨a.val / b.val⟩
def mod (a b : UInt256) : UInt256 := if b.val == 0 then ⟨0⟩ else ⟨a.val % b.val⟩
def modn (a : UInt256) (n : Nat) : UInt256 := ⟨Fin.modn a.val n⟩
def land (a b : UInt256) : UInt256  := ⟨Fin.land a.val b.val⟩
def lor (a b : UInt256) : UInt256   := ⟨Fin.lor a.val b.val⟩
def xor (a b : UInt256) : UInt256   := ⟨Fin.xor a.val b.val⟩
def shiftLeft (a b : UInt256) : UInt256  :=
  if b.val >= 256 then ⟨0⟩ else ⟨a.val <<< b.val⟩
def shiftRight (a b : UInt256) : UInt256 :=
  if b.val >= 256 then ⟨0⟩ else ⟨a.val >>> b.val⟩
def lt (a b : UInt256) : Prop := a.1 < b.1
def le (a b : UInt256) : Prop := a.1 ≤ b.1
def log2 (a : UInt256) : UInt256 := ⟨Fin.log2 a.val⟩

instance : Add UInt256 := ⟨UInt256.add⟩
instance : Sub UInt256 := ⟨UInt256.sub⟩
instance : Mul UInt256 := ⟨UInt256.mul⟩
instance : Div UInt256 := ⟨UInt256.div⟩
instance : Mod UInt256 := ⟨UInt256.mod⟩
instance : HMod UInt256 Nat UInt256 := ⟨UInt256.modn⟩

instance : LT UInt256 where
  lt a b := LT.lt a.val b.val

instance : LE UInt256 where
  le a b := LE.le a.val b.val

instance : DecidableRel (fun a b : UInt256 => a ≤ b) :=
  fun a b => decidable_of_iff (a.val ≤ b.val) Iff.rfl

def complement (a : UInt256) : UInt256 := ⟨0 - (a.val + 1)⟩

def lnot (a : UInt256) : UInt256 := ofNat (UInt256.size - 1) - a

def abs (a : UInt256) : UInt256 :=
  if 2 ^ 255 <= a.toNat
  then ⟨a.val * (-1)⟩
  else a

-- Helper function for signed operations
def sgn (a : UInt256) : Int :=
  if 2 ^ 255 <= a.toNat then -1 else 1

def toSigned (n : Nat) : UInt256 := ofNat n

instance : Complement UInt256 := ⟨UInt256.complement⟩

private def powAux (a : UInt256) (c : UInt256) : Nat → UInt256
  | 0 => a
  | n@(k + 1) => if n % 2 == 1
                 then powAux (a * c) (c * c) (n / 2)
                 else powAux a       (c * c) (n / 2)

def pow (b : UInt256) (n : UInt256) := powAux ⟨1⟩ b n.1

instance : HPow UInt256 UInt256 UInt256 := ⟨pow⟩
instance : AndOp UInt256 := ⟨UInt256.land⟩
instance : OrOp UInt256 := ⟨UInt256.lor⟩
instance : Xor UInt256 := ⟨UInt256.xor⟩
instance : ShiftLeft UInt256 := ⟨UInt256.shiftLeft⟩
instance : ShiftRight UInt256 := ⟨UInt256.shiftRight⟩

-- Mixed-type shift instances for UInt256
instance : HShiftLeft UInt256 UInt8 UInt256 := ⟨fun a b => UInt256.shiftLeft a (UInt256.ofNat b.toNat)⟩
instance : HShiftRight UInt256 UInt8 UInt256 := ⟨fun a b => UInt256.shiftRight a (UInt256.ofNat b.toNat)⟩

instance : Max UInt256 := maxOfLe
instance : Min UInt256 := minOfLe

def eq0 (a : UInt256) : Bool := a == ⟨0⟩

def sdiv (a b : UInt256) : UInt256 :=
  if 2 ^ 255 <= a.toNat then
    if 2 ^ 255 <= b.toNat then
      abs a / abs b
    else ⟨(abs a / b).val * -1⟩
  else
    if 2 ^ 255 <= b.toNat then
      ⟨(a / abs b).val * -1⟩
    else a / b

def smod (a b : UInt256) : UInt256 :=
  if b.toNat == 0 then ⟨0⟩
  else
    toSigned (Int.natAbs (sgn a * (abs a % abs b).toNat))

def exp (a b : UInt256) : UInt256 := pow a b

end UInt256

/-- The size of type `UInt128`, that is, `2^128`. -/
def UInt128.size : Nat :=
  340282366920938463463374607431768211456

structure UInt128 where
  val : Fin UInt128.size
  deriving BEq, Ord

instance : ToString UInt128 where
  toString a := toString a.val

namespace UInt128

def ofNat (n : Nat) : UInt128 := ⟨n % UInt128.size, Nat.mod_lt n (by simp [UInt128.size])⟩

def toNat (u : UInt128) : Nat := u.val.val

instance : Repr UInt128 where
  reprPrec n _ := repr n.toNat

instance {n : Nat} : OfNat UInt128 n := ⟨ofNat n⟩
instance {n : Nat} : OfNat (Fin UInt128.size) n := ⟨(ofNat n).val⟩
instance : Inhabited UInt128 := ⟨ofNat 0⟩

end UInt128

abbrev Nat.toUInt128 : Nat → UInt128 := UInt128.ofNat

namespace UInt128

def add (a b : UInt128) : UInt128 := ⟨a.val + b.val⟩
def sub (a b : UInt128) : UInt128 := ⟨a.val - b.val⟩
def mul (a b : UInt128) : UInt128 := ⟨a.val * b.val⟩
def div (a b : UInt128) : UInt128 := ⟨a.val / b.val⟩
def mod (a b : UInt128) : UInt128 := if b.val == 0 then ⟨0⟩ else ⟨a.val % b.val⟩
def modn (a : UInt128) (n : Nat) : UInt128 := ⟨Fin.modn a.val n⟩
def land (a b : UInt128) : UInt128  := ⟨Fin.land a.val b.val⟩
def lor (a b : UInt128) : UInt128   := ⟨Fin.lor a.val b.val⟩
def xor (a b : UInt128) : UInt128   := ⟨Fin.xor a.val b.val⟩
def shiftLeft (a b : UInt128) : UInt128  :=
  if b.val >= 128 then ⟨0⟩ else ⟨a.val <<< b.val⟩
def shiftRight (a b : UInt128) : UInt128 :=
  if b.val >= 128 then ⟨0⟩ else ⟨a.val >>> b.val⟩
def lt (a b : UInt128) : Prop := a.1 < b.1
def le (a b : UInt128) : Prop := a.1 ≤ b.1
def log2 (a : UInt128) : UInt128 := ⟨Fin.log2 a.val⟩

instance : Add UInt128 := ⟨UInt128.add⟩
instance : Sub UInt128 := ⟨UInt128.sub⟩
instance : Mul UInt128 := ⟨UInt128.mul⟩
instance : Div UInt128 := ⟨UInt128.div⟩
instance : Mod UInt128 := ⟨UInt128.mod⟩
instance : HMod UInt128 Nat UInt128 := ⟨UInt128.modn⟩

instance : LT UInt128 where
  lt a b := LT.lt a.val b.val

instance : LE UInt128 where
  le a b := LE.le a.val b.val

instance : DecidableRel (fun a b : UInt128 => a ≤ b) :=
  fun a b => decidable_of_iff (a.val ≤ b.val) Iff.rfl

def complement (a : UInt128) : UInt128 := ⟨0 - (a.val + 1)⟩

def lnot (a : UInt128) : UInt128 := ofNat (UInt128.size - 1) - a

def abs (a : UInt128) : UInt128 :=
  if 2 ^ 127 <= a.toNat
  then ⟨a.val * (-1)⟩
  else a

-- Helper function for signed operations
def sgn (a : UInt128) : Int :=
  if 2 ^ 127 <= a.toNat then -1 else 1

def toSigned (n : Nat) : UInt128 := ofNat n

instance : Complement UInt128 := ⟨UInt128.complement⟩

private def powAux (a : UInt128) (c : UInt128) : Nat → UInt128
  | 0 => a
  | n@(k + 1) => if n % 2 == 1
                 then powAux (a * c) (c * c) (n / 2)
                 else powAux a       (c * c) (n / 2)

def pow (b : UInt128) (n : UInt128) := powAux ⟨1⟩ b n.1

instance : HPow UInt128 UInt128 UInt128 := ⟨pow⟩
instance : AndOp UInt128 := ⟨UInt128.land⟩
instance : OrOp UInt128 := ⟨UInt128.lor⟩
instance : Xor UInt128 := ⟨UInt128.xor⟩
instance : ShiftLeft UInt128 := ⟨UInt128.shiftLeft⟩
instance : ShiftRight UInt128 := ⟨UInt128.shiftRight⟩

-- Mixed-type shift instances for UInt128
instance : HShiftLeft UInt128 UInt8 UInt128 := ⟨fun a b => UInt128.shiftLeft a (UInt128.ofNat b.toNat)⟩
instance : HShiftRight UInt128 UInt8 UInt128 := ⟨fun a b => UInt128.shiftRight a (UInt128.ofNat b.toNat)⟩

instance : Max UInt128 := maxOfLe
instance : Min UInt128 := minOfLe

def eq0 (a : UInt128) : Bool := a == ⟨0⟩

def sdiv (a b : UInt128) : UInt128 :=
  if 2 ^ 127 <= a.toNat then
    if 2 ^ 127 <= b.toNat then
      abs a / abs b
    else ⟨(abs a / b).val * -1⟩
  else
    if 2 ^ 127 <= b.toNat then
      ⟨(a / abs b).val * -1⟩
    else a / b

def smod (a b : UInt128) : UInt128 :=
  if b.toNat == 0 then ⟨0⟩
  else
    toSigned (Int.natAbs (sgn a * (abs a % abs b).toNat))

def exp (a b : UInt128) : UInt128 := pow a b

end UInt128

def is_equal_Bool (a : Bool) (b : Bool) : Bool :=
    match a, b with
    | true, true => true
    | false, false => true
    | _, _ => false

def is_valid_Bool (a : Bool) : Bool :=
    match a with
    | true => true
    | false => true

def is_equal_u8 (a : UInt8) (b : UInt8) : Bool :=
    sorry

def is_valid_u8 (a : UInt8) : Bool :=
    sorry

def is_equal_u16 (a : UInt16) (b : UInt16) : Bool :=
    sorry

def is_valid_u16 (a : UInt16) : Bool :=
    sorry

def is_equal_u32 (a : UInt32) (b : UInt32) : Bool :=
    sorry

def is_valid_u32 (a : UInt32) : Bool :=
    sorry

def is_equal_u64 (a : UInt64) (b : UInt64) : Bool :=
    sorry

def is_valid_u64 (a : UInt64) : Bool :=
    sorry

def is_equal_u128 (a : UInt128) (b : UInt128) : Bool :=
    sorry

def is_valid_u128 (a : UInt128) : Bool :=
    sorry

 def is_equal_u256 (a : UInt256) (b : UInt256) : Bool :=
     sorry

 def is_valid_u256 (a : UInt256) : Bool :=
     sorry

def m1_integer_Integer : Type := Int

instance : DecidableEq m1_integer_Integer := Int.decEq

instance : BEq m1_integer_Integer where
  beq a b := decide (a = b)

def m1_integer_from_u8 (x : UInt8) : m1_integer_Integer :=
    sorry

def m1_integer_from_u16 (x : UInt16) : m1_integer_Integer :=
    sorry

def m1_integer_from_u32 (x : UInt32) : m1_integer_Integer :=
    sorry

def m1_integer_from_u64 (x : UInt64) : m1_integer_Integer :=
    sorry

def m1_integer_from_u128 (x : UInt128) : m1_integer_Integer :=
    sorry

def m1_integer_from_u256 (x : UInt256) : m1_integer_Integer :=
    sorry

def m1_integer_to_u8 (x : m1_integer_Integer) : UInt8 :=
    sorry

def m1_integer_to_u16 (x : m1_integer_Integer) : UInt16 :=
    sorry

def m1_integer_to_u32 (x : m1_integer_Integer) : UInt32 :=
    sorry

def m1_integer_to_u64 (x : m1_integer_Integer) : UInt64 :=
    sorry

def m1_integer_to_u128 (x : m1_integer_Integer) : UInt128 :=
    sorry

def m1_integer_to_u256 (x : m1_integer_Integer) : UInt256 :=
    sorry

def m1_integer_add (x : m1_integer_Integer) (y : m1_integer_Integer) : m1_integer_Integer :=
    sorry

def m1_integer_sub (x : m1_integer_Integer) (y : m1_integer_Integer) : m1_integer_Integer :=
    sorry

def m1_integer_mul (x : m1_integer_Integer) (y : m1_integer_Integer) : m1_integer_Integer :=
    sorry

def m1_integer_div (x : m1_integer_Integer) (y : m1_integer_Integer) : m1_integer_Integer :=
    sorry

def m1_integer_mod (x : m1_integer_Integer) (y : m1_integer_Integer) : m1_integer_Integer :=
    sorry

def m1_integer_gt (x : m1_integer_Integer) (y : m1_integer_Integer) : Bool :=
    sorry

def m1_integer_gte (x : m1_integer_Integer) (y : m1_integer_Integer) : Bool :=
    sorry

def m1_integer_lt (x : m1_integer_Integer) (y : m1_integer_Integer) : Bool :=
    sorry

def m1_integer_lte (x : m1_integer_Integer) (y : m1_integer_Integer) : Bool :=
    sorry

def m1_integer_neg (x : m1_integer_Integer) : m1_integer_Integer :=
    sorry

def m1_integer_pow (x : m1_integer_Integer) (y : m1_integer_Integer) : m1_integer_Integer :=
    sorry
