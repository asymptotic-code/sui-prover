module std::bit_vector_spec {
  use std::bit_vector;
  use std::bit_vector::BitVector;

  #[spec(prove)]
  public fun new_spec(length: u64): BitVector {
    let result = bit_vector::new(length);
    result
  }

  #[spec(prove)]
  fun set_spec(bitvector: &mut BitVector, bit_index: u64) {
    bit_vector::set(bitvector, bit_index);
  }

  #[spec(prove)]
  fun unset_spec(bitvector: &mut BitVector, bit_index: u64) {
    bit_vector::unset(bitvector, bit_index);
  }

  #[spec(prove)]
  fun shift_left_spec(bitvector: &mut BitVector, amount: u64) {
    bit_vector::shift_left(bitvector, amount);
  }

  #[spec(prove)]
  fun is_index_set_spec(bitvector: &BitVector, bit_index: u64): bool {
    let result = bit_vector::is_index_set(bitvector, bit_index);
    result
  }

  #[spec(prove)]
  fun length_spec(bitvector: &BitVector): u64 {
    let result = bit_vector::length(bitvector);
    result
  }

  #[spec(prove)]
  fun longest_set_sequence_starting_at_spec(bitvector: &BitVector, start_index: u64): u64 {
    let result = bit_vector::longest_set_sequence_starting_at(bitvector, start_index);
    result
  }
}
