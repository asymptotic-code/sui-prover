module std::u8_spec {
  use std::u8;

  #[spec(prove)]
  fun max_spec(x: u8, y: u8): u8 {
        let result = u8::max(x, y);
        result
  }
}
