module std::u128_spec {
  use std::u128;
  use std::string::String;
  use std::option::Option;

  #[spec(prove)]
  fun bitwise_not_spec(x: u128): u128 {
        let result = u128::bitwise_not(x);
        result
  }

  #[spec(prove)]
  fun max_spec(x: u128, y: u128): u128 {
        let result = u128::max(x, y);
        result
  }

  #[spec(prove)]
  fun min_spec(x: u128, y: u128): u128 {
        let result = u128::min(x, y);
        result
  }

  #[spec(prove)]
  fun diff_spec(x: u128, y: u128): u128 {
        let result = u128::diff(x, y);
        result
  }

  #[spec(prove)]
  fun divide_and_round_up_spec(x: u128, y: u128): u128 {
        let result = u128::divide_and_round_up(x, y);
        result
  }

  #[spec(prove)]
  fun pow_spec(base: u128, exponent: u8): u128 {
        let result = u128::pow(base, exponent);
        result
  }

  #[spec(prove)]
  fun sqrt_spec(x: u128): u128 {
        let result = u128::sqrt(x);
        result
  }

  #[spec(prove)]
  fun try_as_u8_spec(x: u128): Option<u8> {
        let result = u128::try_as_u8(x);
        result
  }

  #[spec(prove)]
  fun try_as_u16_spec(x: u128): Option<u16> {
        let result = u128::try_as_u16(x);
        result
  }

  #[spec(prove)]
  fun try_as_u32_spec(x: u128): Option<u32> {
        let result = u128::try_as_u32(x);
        result
  }

  #[spec(prove)]
  fun try_as_u64_spec(x: u128): Option<u64> {
        let result = u128::try_as_u64(x);
        result
  }

  #[spec(prove)]
  fun to_string_spec(x: u128): String {
        let result = u128::to_string(x);
        result
  }
}
