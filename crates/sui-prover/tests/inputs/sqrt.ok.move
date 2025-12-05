module 0x42::foo;

use std::integer::Integer;
use std::real::Real;
use prover::prover::ensures;

public fun foo(a: Integer): Integer {
  a.sqrt()
}


public fun bar(a: Real): Real {
  a.sqrt()
}

#[spec(prove)]
public fun spec_i_d() {
  ensures(foo(16u8.to_int()) == 4u8.to_int());
}

#[spec(prove)]
public fun spec_i_b() {
  ensures(foo(17u8.to_int()).gte(4u8.to_int()));
  ensures(foo(17u8.to_int()).lt(5u8.to_int()));
}

#[spec(prove)]
public fun spec_r_d() {
  ensures(bar(16u8.to_real()) == 4u8.to_real());
}

#[spec(prove)]
public fun spec_r_b() {
  ensures(bar(17u8.to_real()).gt(4u8.to_real()));
  ensures(bar(17u8.to_real()).lt(5u8.to_real()));
}
