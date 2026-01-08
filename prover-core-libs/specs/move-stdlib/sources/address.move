module std::address_spec {
  use std::address;

  #[spec(prove)]
  fun length_spec(): u64 {
        let result = address::length();
        result
  }
}
