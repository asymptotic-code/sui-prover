module 0x42::foo;

#[spec_only]
use prover::prover::ensures;

public fun factorial(x: u64): u64 {
  if (x == 0) {
    1
  } else {
    x * factorial(x - 1)
  }
}

#[spec(prove)]
public fun my_spec_simple() {
  ensures(factorial(5) == 120);
}


public fun factorial_helper(x: u64): u64 {
  x * factorial_complex(x)
}

public fun factorial_complex(x: u64): u64 {
  if (x == 0) {
    1
  } else {
    factorial_helper(x - 1)
  }
}

#[spec(prove)]
public fun my_spec_complex() {
  ensures(factorial_complex(5) == 120);
}
