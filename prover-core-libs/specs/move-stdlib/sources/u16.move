module std::u16_spec {
  use std::u16;
  use std::string::String;
  use std::option::Option;

  #[spec(prove)]
  fun bitwise_not_spec(x: u16): u16 {
        let result = u16::bitwise_not(x);
        result
  }

  #[spec(prove)]
  fun max_spec(x: u16, y: u16): u16 {
        let result = u16::max(x, y);
        result
  }

  #[spec(prove)]
  fun min_spec(x: u16, y: u16): u16 {
        let result = u16::min(x, y);
        result
  }

  #[spec(prove)]
  fun diff_spec(x: u16, y: u16): u16 {
        let result = u16::diff(x, y);
        result
  }

  #[spec(prove)]
  fun divide_and_round_up_spec(x: u16, y: u16): u16 {
        let result = u16::divide_and_round_up(x, y);
        result
  }

  #[spec(prove)]
  fun pow_spec(base: u16, exponent: u8): u16 {
        let result = u16::pow(base, exponent);
        result
  }

  #[spec(prove)]
  fun sqrt_spec(x: u16): u16 {
        let result = u16::sqrt(x);
        result
  }

  #[spec(prove)]
  fun try_as_u8_spec(x: u16): Option<u8> {
        let result = u16::try_as_u8(x);
        result
  }

  #[spec(prove)]
  fun to_string_spec(x: u16): String {
        let result = u16::to_string(x);
        result
  }
}
