import Prelude.UInt256

-- The size of type `UInt128`, that is, `2^128`.
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

-- Conversion to UInt256
def toUInt256 (a : UInt128) : UInt256 := UInt256.ofNat a.toNat

end UInt128

-- Conversion from UInt256 to UInt128 (defined here to avoid circular import)
namespace UInt256
def toUInt128 (a : UInt256) : UInt128 := UInt128.ofNat a.toNat
end UInt256

namespace UInt128

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

instance : DecidableRel (fun a b : UInt128 => a < b) :=
  fun a b => decidable_of_iff (a.val < b.val) Iff.rfl

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
instance : XorOp UInt128 := ⟨UInt128.xor⟩
instance : ShiftLeft UInt128 := ⟨UInt128.shiftLeft⟩
instance : ShiftRight UInt128 := ⟨UInt128.shiftRight⟩

-- Mixed-type shift instances for UInt128
instance : HShiftLeft UInt128 UInt8 UInt128 := ⟨fun a b => UInt128.shiftLeft a (UInt128.ofNat b.toNat)⟩
instance : HShiftRight UInt128 UInt8 UInt128 := ⟨fun a b => UInt128.shiftRight a (UInt128.ofNat b.toNat)⟩
instance : HShiftLeft UInt128 Nat UInt128 := ⟨fun a b => UInt128.shiftLeft a (UInt128.ofNat b)⟩
instance : HShiftRight UInt128 Nat UInt128 := ⟨fun a b => UInt128.shiftRight a (UInt128.ofNat b)⟩

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
