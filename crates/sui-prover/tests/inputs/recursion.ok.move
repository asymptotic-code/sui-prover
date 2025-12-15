module 0x42::foo;

#[spec_only]
use prover::prover::ensures;

// not inlined
public fun factorial(x: u64): u64 {
  if (x == 0) {
    1
  } else {
    x * factorial(x - 1)
  }
}

#[spec(prove)]
public fun my_spec() {
  ensures(5 * 5 == 25);
}
