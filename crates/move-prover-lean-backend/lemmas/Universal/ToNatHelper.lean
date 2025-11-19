import Lemmas.Universal.UInt256
import Lemmas.Universal.UInt128

-- Helper to convert both typed integers and Nat to Nat
-- Used for shift amounts and abort codes
class ToNatHelper (α : Type) where
  toNatHelperImpl : α → Nat

instance : ToNatHelper Nat where
  toNatHelperImpl n := n

instance : ToNatHelper UInt8 where
  toNatHelperImpl n := n.toNat

instance : ToNatHelper UInt16 where
  toNatHelperImpl n := n.toNat

instance : ToNatHelper UInt32 where
  toNatHelperImpl n := n.toNat

instance : ToNatHelper UInt64 where
  toNatHelperImpl n := n.toNat

instance : ToNatHelper UInt128 where
  toNatHelperImpl n := n.toNat

instance : ToNatHelper UInt256 where
  toNatHelperImpl n := n.toNat

instance : ToNatHelper Int8 where
  toNatHelperImpl n := n.toNatClampNeg

instance : ToNatHelper Int16 where
  toNatHelperImpl n := n.toNatClampNeg

instance : ToNatHelper Int32 where
  toNatHelperImpl n := n.toNatClampNeg

instance : ToNatHelper Int64 where
  toNatHelperImpl n := n.toNatClampNeg

-- Standalone function that uses typeclass resolution
-- Must be defined AFTER all instances to avoid namespace issues
def toNatHelper {α : Type} [inst : ToNatHelper α] (x : α) : Nat :=
  inst.toNatHelperImpl x
