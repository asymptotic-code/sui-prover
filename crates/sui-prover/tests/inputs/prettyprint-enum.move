module 0x42::foo;

use prover::prover::{ensures, requires};
use prover::log;

public enum MyEnum has copy, drop {
    A(u64),
    B(u64),
}

public fun foo(x: u64): MyEnum {
    if (x % 2 == 0) {
        MyEnum::A(x)
    } else {
        MyEnum::B(0)
    }
}

#[spec(prove)]
public fun foo_spec(x: u64): MyEnum {
    let res = foo(x);
    log::var<MyEnum>(&res);
    ensures(res == MyEnum::A(x));
    res
}
