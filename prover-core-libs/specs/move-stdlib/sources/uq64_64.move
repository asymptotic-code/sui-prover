module std::uq64_64_spec {
  use std::uq64_64::{Self, UQ64_64};

  #[spec(prove)]
  fun from_quotient_spec(numerator: u128, denominator: u128): UQ64_64 {
    let result = uq64_64::from_quotient(numerator, denominator);
    result
  }

  #[spec(prove)]
  fun from_int_spec(integer: u64): UQ64_64 {
    let result = uq64_64::from_int(integer);
    result
  }

  #[spec(prove)]
  fun add_spec(a: UQ64_64, b: UQ64_64): UQ64_64 {
    let result = uq64_64::add(a, b);
    result
  }

  #[spec(prove)]
  fun sub_spec(a: UQ64_64, b: UQ64_64): UQ64_64 {
    let result = uq64_64::sub(a, b);
    result
  }

  #[spec(prove)]
  fun mul_spec(a: UQ64_64, b: UQ64_64): UQ64_64 {
    let result = uq64_64::mul(a, b);
    result
  }

  #[spec(prove)]
  fun div_spec(a: UQ64_64, b: UQ64_64): UQ64_64 {
    let result = uq64_64::div(a, b);
    result
  }

  #[spec(prove)]
  fun to_int_spec(a: UQ64_64): u64 {
    let result = uq64_64::to_int(a);
    result
  }

  #[spec(prove)]
  fun int_mul_spec(val: u128, multiplier: UQ64_64): u128 {
    let result = uq64_64::int_mul(val, multiplier);
    result
  }

  #[spec(prove)]
  fun int_div_spec(val: u128, divisor: UQ64_64): u128 {
    let result = uq64_64::int_div(val, divisor);
    result
  }

  #[spec(prove)]
  fun le_spec(a: UQ64_64, b: UQ64_64): bool {
    let result = uq64_64::le(a, b);
    result
  }

  #[spec(prove)]
  fun lt_spec(a: UQ64_64, b: UQ64_64): bool {
    let result = uq64_64::lt(a, b);
    result
  }

  #[spec(prove)]
  fun ge_spec(a: UQ64_64, b: UQ64_64): bool {
    let result = uq64_64::ge(a, b);
    result
  }

  #[spec(prove)]
  fun gt_spec(a: UQ64_64, b: UQ64_64): bool {
    let result = uq64_64::gt(a, b);
    result
  }

  #[spec(prove)]
  fun to_raw_spec(a: UQ64_64): u128 {
    let result = uq64_64::to_raw(a);
    result
  }

  #[spec(prove)]
  fun from_raw_spec(raw_value: u128): UQ64_64 {
    let result = uq64_64::from_raw(raw_value);
    result
  }
}
