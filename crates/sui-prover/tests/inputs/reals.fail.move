module 0x42::foo;

use prover::prover::{ensures, requires};
use prover::log;

public fun foo(x: u64): u64 {
  x + 1
}

#[spec_only]
fun show_real(the_real: std::real::Real): std::real::Real {
  the_real
}

#[spec(prove)]
public fun foo_spec(x: u64): u64 {
  requires(x < std::u64::max_value!());
  let res = foo(x);
  let y_real = show_real(1u64.to_real().div(7u64.to_real()));
  log::var<std::real::Real>(&y_real);
  ensures(y_real  != y_real);
  res
}
