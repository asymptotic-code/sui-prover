#[allow(unused_function)]
module 0x42::working_test;

use prover::prover::{requires, ensures};

public fun eq_address(x: Option<address>, y: Option<address>): bool {
    *x.borrow() == *y.borrow()
}

#[spec(prove)]
public fun eq_address_spec(x: Option<address>, y: Option<address>): bool {
    requires(x.is_some());
    requires(y.is_some());
    let r = eq_address(x, y);
    ensures(r == (x != y));
    r
}
