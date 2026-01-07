module std::u32_spec {
  use std::u32;
  use std::string::String;
  use std::option::Option;

  #[spec(prove)]
  fun bitwise_not_spec(x: u32): u32 {
        let result = u32::bitwise_not(x);
        result
  }

  #[spec(prove)]
  fun max_spec(x: u32, y: u32): u32 {
        let result = u32::max(x, y);
        result
  }

  #[spec(prove)]
  fun min_spec(x: u32, y: u32): u32 {
        let result = u32::min(x, y);
        result
  }

  #[spec(prove)]
  fun diff_spec(x: u32, y: u32): u32 {
        let result = u32::diff(x, y);
        result
  }

  #[spec(prove)]
  fun divide_and_round_up_spec(x: u32, y: u32): u32 {
        let result = u32::divide_and_round_up(x, y);
        result
  }

  #[spec(prove)]
  fun pow_spec(base: u32, exponent: u8): u32 {
        let result = u32::pow(base, exponent);
        result
  }

  #[spec(prove)]
  fun sqrt_spec(x: u32): u32 {
        let result = u32::sqrt(x);
        result
  }

  #[spec(prove)]
  fun try_as_u8_spec(x: u32): Option<u8> {
        let result = u32::try_as_u8(x);
        result
  }

  #[spec(prove)]
  fun try_as_u16_spec(x: u32): Option<u16> {
        let result = u32::try_as_u16(x);
        result
  }

  #[spec(prove)]
  fun to_string_spec(x: u32): String {
        let result = u32::to_string(x);
        result
  }
}
