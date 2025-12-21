-- Native implementations for prover::search module
-- Provides generic binary search algorithms with proven termination

import Prelude.BoundedNat
import Impls.IntegerMate.I32

namespace SearchOps

-- ============================================================================
-- Generic Binary Search
-- ============================================================================

/--
Generic binary search over I32 range with fuel-based termination.
Finds the largest value `x` in `[low, high]` such that `f(x) ≤ target`.

Parameters:
- `f`: Function from I32 to some ordered type α
- `target`: Target value to search for
- `low`: Lower bound (inclusive)
- `high`: Upper bound (inclusive)
- `fuel`: Maximum iterations (prevents infinite loops)

Returns: The largest `x` where `f(x) ≤ target`, or `low` if no such value exists.
-/
def binary_search {α : Type} [LE α] [DecidableRel (· ≤ · : α → α → Prop)]
    (f : I32.I32 → α) (target : α) (low : I32.I32) (high : I32.I32) (fuel : Nat) : I32.I32 :=
  match fuel with
  | 0 => low
  | fuel' + 1 =>
    if I32.lt low high then
      -- Calculate mid = low + (high - low + 1) / 2 (round up)
      -- Using raw UInt32 operations to avoid dependency on I32 arithmetic functions
      let low_bits := I32.as_u32 low
      let high_bits := I32.as_u32 high
      let diff := high_bits - low_bits
      let diff_plus_1 := diff + 1
      let half := diff_plus_1 / 2
      let mid_bits := low_bits + half
      let mid := I32.from_u32 mid_bits

      if f mid ≤ target then
        -- mid is valid, search upper half
        binary_search f target mid high fuel'
      else
        -- mid is too high, search lower half
        let new_high_bits := mid_bits - 1
        let new_high := I32.from_u32 new_high_bits
        binary_search f target low new_high fuel'
    else
      low

-- ============================================================================
-- Specialized Binary Search for BoundedNat (2^128)
-- ============================================================================

-- For binary search with u128 values (BoundedNat (2^128))
-- This is the most commonly used variant for tick math and price calculations
def binary_search_u128 (f : I32.I32 → BoundedNat (2^128)) (target : BoundedNat (2^128))
    (low : I32.I32) (high : I32.I32) : I32.I32 :=
  -- max I32 range is 2^32, so log2(2^32) = 32 iterations max
  binary_search f target low high 32

end SearchOps
