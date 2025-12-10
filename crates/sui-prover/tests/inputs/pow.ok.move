module 0x42::foo;

use std::integer::Integer;
use std::real::Real;
use prover::prover::ensures;

public fun foo(a: Integer, p: u8): Integer {
  a.pow(p.to_int())
}


public fun bar(a: Real, p: u8): Real {
  a.exp(p.to_int())
}

#[spec(prove)]
public fun spec_i_d() {
  ensures(foo(5u8.to_int(), 2) == 25u8.to_int());
  ensures(foo(2u8.to_int(), 4) == 16u8.to_int());
  ensures(foo(1u8.to_int(), 2) == 1u8.to_int());
  ensures(foo(1u8.to_int(), 0) == 1u8.to_int());
}

#[spec(prove)]
public fun spec_r_d() {
  ensures(bar(6u8.to_real(), 2) == 36u8.to_real());
  ensures(bar(2u8.to_real(), 3) == 8u8.to_real());
  ensures(bar(1u8.to_real(), 2) == 1u8.to_real());
  ensures(bar(1u8.to_real(), 0) == 1u8.to_real());
}
