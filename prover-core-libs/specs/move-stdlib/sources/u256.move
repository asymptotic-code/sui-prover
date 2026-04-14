module std::u256_spec {
  use std::u256;
  use std::string::String;
  use std::option::Option;

  #[spec(prove)]
  fun bitwise_not_spec(x: u256): u256 {
    let result = u256::bitwise_not(x);
    result
  }

  #[spec(prove)]
  fun max_spec(x: u256, y: u256): u256 {
    let result = u256::max(x, y);
    result
  }

  #[spec(prove)]
  fun min_spec(x: u256, y: u256): u256 {
    let result = u256::min(x, y);
    result
  }

  #[spec(prove)]
  fun diff_spec(x: u256, y: u256): u256 {
    let result = u256::diff(x, y);
    result
  }

  #[spec(prove)]
  fun divide_and_round_up_spec(x: u256, y: u256): u256 {
    let result = u256::divide_and_round_up(x, y);
    result
  }

  #[spec(prove)]
  fun pow_spec(base: u256, exponent: u8): u256 {
    let result = u256::pow(base, exponent);
    result
  }

  #[spec(prove)]
  fun try_as_u8_spec(x: u256): Option<u8> {
    let result = u256::try_as_u8(x);
    result
  }

  #[spec(prove)]
  fun try_as_u16_spec(x: u256): Option<u16> {
    let result = u256::try_as_u16(x);
    result
  }

  #[spec(prove)]
  fun try_as_u32_spec(x: u256): Option<u32> {
    let result = u256::try_as_u32(x);
    result
  }

  #[spec(prove)]
  fun try_as_u64_spec(x: u256): Option<u64> {
    let result = u256::try_as_u64(x);
    result
  }

  #[spec(prove)]
  fun try_as_u128_spec(x: u256): Option<u128> {
    let result = u256::try_as_u128(x);
    result
  }

  #[spec(prove)]
  fun to_string_spec(x: u256): String {
    let result = u256::to_string(x);
    result
  }
}
