module std::fixed_point32_spec {
  use std::fixed_point32::{Self, FixedPoint32};

  #[spec(prove)]
  fun multiply_u64_spec(val: u64, multiplier: FixedPoint32): u64 {
        let result = fixed_point32::multiply_u64(val, multiplier);
        result
  }

  #[spec(prove)]
  fun divide_u64_spec(val: u64, divisor: FixedPoint32): u64 {
        let result = fixed_point32::divide_u64(val, divisor);
        result
  }

  #[spec(prove)]
  fun create_from_rational_spec(numerator: u64, denominator: u64): FixedPoint32 {
        let result = fixed_point32::create_from_rational(numerator, denominator);
        result
  }

  #[spec(prove)]
  fun create_from_raw_value_spec(value: u64): FixedPoint32 {
        let result = fixed_point32::create_from_raw_value(value);
        result
  }

  #[spec(prove)]
  fun get_raw_value_spec(num: FixedPoint32): u64 {
        let result = fixed_point32::get_raw_value(num);
        result
  }

  #[spec(prove)]
  fun is_zero_spec(num: FixedPoint32): bool {
        let result = fixed_point32::is_zero(num);
        result
  }
}
