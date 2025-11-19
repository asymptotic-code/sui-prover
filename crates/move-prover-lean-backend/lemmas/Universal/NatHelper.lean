-- Copyright (c) Asymptotic Labs
-- SPDX-License-Identifier: Apache-2.0

-- NatHelper: Automatic handling of Nat conversions
--
-- This module provides helpers for converting between Nat and UInt types
-- without explicit .toNat calls, avoiding the "Nat.toNat doesn't exist" error.

namespace NatHelper

-- Convert a Nat to UInt8
def natToUInt8 (n : Nat) : UInt8 := n.toUInt8

-- Convert a Nat to UInt16
def natToUInt16 (n : Nat) : UInt16 := n.toUInt16

-- Convert a Nat to UInt32
def natToUInt32 (n : Nat) : UInt32 := n.toUInt32

-- Convert a Nat to UInt64
def natToUInt64 (n : Nat) : UInt64 := n.toUInt64

-- Convert a Nat to UInt128
def natToUInt128 (n : Nat) : UInt128 := n.toUInt128

-- Convert a Nat to UInt256
def natToUInt256 (n : Nat) : UInt256 := n.toUInt256

end NatHelper
