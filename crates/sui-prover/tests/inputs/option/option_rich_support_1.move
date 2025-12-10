#[allow(unused_function)]
module 0x42::working_test;

use prover::prover::{requires, ensures};

public fun eq_bool(x: Option<bool>, y: Option<bool>): bool {
    *x.borrow() == *y.borrow()
}

public fun eq_num(x: Option<u64>, y: Option<u64>): bool {
    *x.borrow() == *y.borrow()
}

#[spec(prove)]
public fun eq_bool_spec(x: Option<bool>, y: Option<bool>): bool {
    requires(x.is_some() && y.is_some());
    let r = eq_bool(x, y);
    ensures(r == (x==y));
    r
}

#[spec(prove)]
public fun eq_num_spec(x: Option<u64>, y: Option<u64>): bool {
    requires(x.is_some() && y.is_some());
    requires(x != y);
    let r = eq_num(x, y);
    ensures(!r);
    r
}
