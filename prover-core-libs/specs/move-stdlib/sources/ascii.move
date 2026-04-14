module std::ascii_spec {
  use std::ascii;

  #[spec(prove)]
  fun char_spec(byte: u8): ascii::Char {
        let result = ascii::char(byte);
        result
  }

  #[spec(prove)]
  fun string_spec(bytes: vector<u8>): ascii::String {
        let result = ascii::string(bytes);
        result
  }

  #[spec(prove)]
  fun try_string_spec(bytes: vector<u8>): Option<ascii::String> {
        let result = ascii::try_string(bytes);
        result
  }

  #[spec(prove)]
  fun all_characters_printable_spec(string: &ascii::String): bool {
        let result = ascii::all_characters_printable(string);
        result
  }

  #[spec(prove)]
  fun push_char_spec(string: &mut ascii::String, char: ascii::Char) {
        ascii::push_char(string, char);
  }

  #[spec(prove)]
  fun pop_char_spec(string: &mut ascii::String): ascii::Char {
        let result = ascii::pop_char(string);
        result
  }

  #[spec(prove)]
  fun length_spec(string: &ascii::String): u64 {
        let result = ascii::length(string);
        result
  }

  #[spec(prove)]
  fun append_spec(string: &mut ascii::String, other: ascii::String) {
        ascii::append(string, other);
  }

  #[spec(prove)]
  fun insert_spec(s: &mut ascii::String, at: u64, o: ascii::String) {
        ascii::insert(s, at, o);
  }

  #[spec(prove)]
  fun substring_spec(string: &ascii::String, i: u64, j: u64): ascii::String {
        let result = ascii::substring(string, i, j);
        result
  }

  #[spec(prove)]
  fun as_bytes_spec(string: &ascii::String): &vector<u8> {
        let result = ascii::as_bytes(string);
        result
  }

  #[spec(prove)]
  fun into_bytes_spec(string: ascii::String): vector<u8> {
        let result = ascii::into_bytes(string);
        result
  }

  #[spec(prove)]
  fun byte_spec(char: ascii::Char): u8 {
        let result = ascii::byte(char);
        result
  }

  #[spec(prove)]
  fun is_valid_char_spec(b: u8): bool {
        let result = ascii::is_valid_char(b);
        result
  }

  #[spec(prove)]
  fun is_printable_char_spec(byte: u8): bool {
        let result = ascii::is_printable_char(byte);
        result
  }

  #[spec(prove)]
  fun is_empty_spec(string: &ascii::String): bool {
        let result = ascii::is_empty(string);
        result
  }

  #[spec(prove)]
  fun to_uppercase_spec(string: &ascii::String): ascii::String {
        let result = ascii::to_uppercase(string);
        result
  }

  #[spec(prove)]
  fun to_lowercase_spec(string: &ascii::String): ascii::String {
        let result = ascii::to_lowercase(string);
        result
  }

  #[spec(prove)]
  fun index_of_spec(string: &ascii::String, substr: &ascii::String): u64 {
        let result = ascii::index_of(string, substr);
        result
  }
}
