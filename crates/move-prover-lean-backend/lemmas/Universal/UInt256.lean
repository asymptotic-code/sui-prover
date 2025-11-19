import Init.Data.Nat.Div

-- The size of type `UInt256`, that is, `2^256`.
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

instance : DecidableRel (fun a b : UInt256 => a < b) :=
  fun a b => decidable_of_iff (a.val < b.val) Iff.rfl

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
instance : XorOp UInt256 := ⟨UInt256.xor⟩
instance : ShiftLeft UInt256 := ⟨UInt256.shiftLeft⟩
instance : ShiftRight UInt256 := ⟨UInt256.shiftRight⟩

-- Mixed-type shift instances for UInt256
instance : HShiftLeft UInt256 UInt8 UInt256 := ⟨fun a b => UInt256.shiftLeft a (UInt256.ofNat b.toNat)⟩
instance : HShiftRight UInt256 UInt8 UInt256 := ⟨fun a b => UInt256.shiftRight a (UInt256.ofNat b.toNat)⟩
instance : HShiftLeft UInt256 Nat UInt256 := ⟨fun a b => UInt256.shiftLeft a (UInt256.ofNat b)⟩
instance : HShiftRight UInt256 Nat UInt256 := ⟨fun a b => UInt256.shiftRight a (UInt256.ofNat b)⟩

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
