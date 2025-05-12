module 0x42::foo;

#[spec_only]
use prover::prover::{ensures, requires};

public fun foo(x: u64): u64 {
    x + 1
}

#[spec(prove)]
public fun foo_spec(x: u64): u64 {
    requires(x < std::u64::max_value!());
    let res = foo(x);
    let x_int = x.to_int();
    let res_int = res.to_int();
    prover::log::text(b"Checking value of x");
    ensures(res_int == 0u64.to_int());
    res
}
