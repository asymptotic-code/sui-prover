-- Native implementations for i32::I32 module

import Prelude.Helpers

namespace I32

-- abs: Return the absolute value of an I32
-- If the value is negative, negate it; otherwise return as-is
partial def abs (v : I32) : (Except AbortCode I32) :=
  if is_neg v then
    wrapping_sub (I32.mk 0) v
  else
    pure v

end I32
