module 0x42::foo;

#[spec_only]
use prover::prover::{ensures};

public fun foo(x: u64): u64 {
  x & 1u64
}

#[spec(prove)]
public fun foo_spec(x: u64): u64 {
  let res = foo(x);
  if (x % 2u64 == 0u64  ) {
    ensures(res == 0u64);
  } else {
    ensures(res == 1u64);
  };
  res
}

#[spec(prove)]
public fun foo2_spec(x: u64): u64 {
  let res = foo(x);
  if (x % 2u64 == 0u64  ) {
    ensures(res == 1u64);
  } else {
    ensures(res == 0u64);
  };
  res
}