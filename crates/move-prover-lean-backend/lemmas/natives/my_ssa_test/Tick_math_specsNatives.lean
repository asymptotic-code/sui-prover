-- Native implementations for tick_math_specs module
-- Provides binary search using the generic SearchOps implementation

import Prelude.BoundedNat
import Impls.IntegerMate.I32
import Impls.Prover.SearchNatives
import Impls.Prover.MoveReal

namespace Tick_math_specsOps

-- Define get_sqrt_price_at_tick_math directly here so binary_search_tick can use it
-- This is the mathematical specification: floor(1.0001^(tick/2) * 2^64)
noncomputable def get_sqrt_price_at_tick_math (tick : I32.I32) : BoundedNat (2^128) :=
  let tick_rat := MoveReal.from_i32_bits (I32.as_u32 tick)
  let base := MoveReal.from_fraction (MoveReal.from_u64 ⟨10001, by decide⟩) (MoveReal.from_u64 ⟨10000, by decide⟩)
  let two := MoveReal.from_u64 ⟨2, by decide⟩
  let exponent := MoveReal.div tick_rat two
  MoveReal.floor_u128 (MoveReal.mul (MoveReal.pow base exponent) (MoveReal.from_u128 ⟨18446744073709551616, by native_decide⟩))

-- Binary search for tick values using get_sqrt_price_at_tick_math
-- This is noncomputable because get_sqrt_price_at_tick_math uses Real arithmetic
noncomputable def binary_search_tick (target_price : BoundedNat (2^128)) (low : I32.I32) (high : I32.I32) : I32.I32 :=
  SearchOps.binary_search get_sqrt_price_at_tick_math target_price low high 32

end Tick_math_specsOps
