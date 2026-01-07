module std::bit_vector_spec {
  use std::bit_vector;
  use std::bit_vector::BitVector;

  #[spec(prove)]
  public fun new_spec(length: u64): BitVector {
    let result = bit_vector::new(5);
    result
  }
}
