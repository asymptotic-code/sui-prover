module 0x42::foo;

use prover::prover::{requires, ensures};

use sui::dynamic_field as df;

public struct Foo has key {
    id: UID,
}

fun remove_opt_when_present(x: &mut Foo): Option<u8> {
    df::remove_opt<u64, u8>(&mut x.id, 10)
}

#[mode(spec), ext(spec(prove))]
fun remove_opt_when_present_spec(x: &mut Foo): Option<u8> {
    requires(df::exists_with_type<u64, u8>(&x.id, 10));
    requires(df::borrow<u64, u8>(&x.id, 10) == 5);
    let res = remove_opt_when_present(x);
    ensures(!df::exists_with_type<u64, u8>(&x.id, 10));
    ensures(res == option::some(5));
    res
}

fun remove_opt_when_absent(x: &mut Foo): Option<u8> {
    df::remove_opt<u64, u8>(&mut x.id, 10)
}

#[mode(spec), ext(spec(prove))]
fun remove_opt_when_absent_spec(x: &mut Foo): Option<u8> {
    requires(!df::exists_with_type<u64, u8>(&x.id, 10));
    let res = remove_opt_when_absent(x);
    ensures(!df::exists_with_type<u64, u8>(&x.id, 10));
    ensures(res == option::none());
    res
}
