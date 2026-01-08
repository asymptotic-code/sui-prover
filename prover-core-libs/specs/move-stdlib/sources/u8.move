module std::u8_spec {
  use std::u8;
  use std::string::String;

  #[spec(prove)]
  fun bitwise_not_spec(x: u8): u8 {
        let result = u8::bitwise_not(x);
        result
  }

  #[spec(prove)]
  fun max_spec(x: u8, y: u8): u8 {
        let result = u8::max(x, y);
        result
  }

  #[spec(prove)]
  fun min_spec(x: u8, y: u8): u8 {
        let result = u8::min(x, y);
        result
  }

  #[spec(prove)]
  fun diff_spec(x: u8, y: u8): u8 {
        let result = u8::diff(x, y);
        result
  }

  #[spec(prove)]
  fun divide_and_round_up_spec(x: u8, y: u8): u8 {
        let result = u8::divide_and_round_up(x, y);
        result
  }

  #[spec(prove)]
  fun pow_spec(base: u8, exponent: u8): u8 {
        let result = u8::pow(base, exponent);
        result
  }

  #[spec(prove)]
  fun sqrt_spec(x: u8): u8 {
        let result = u8::sqrt(x);
        result
  }

  #[spec(prove)]
  fun to_string_spec(x: u8): String {
        let result = u8::to_string(x);
        result
  }
}
