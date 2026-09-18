module 0x42::foo;

use prover::prover::{requires, ensures};

use sui::dynamic_object_field as dof;

public struct Foo has key {
    id: UID,
}

public struct Bar has key, store {
    id: UID,
    bar: u64,
}

fun remove_opt_when_absent(x: &mut Foo): Option<Bar> {
    dof::remove_opt<u64, Bar>(&mut x.id, 10)
}

#[mode(spec), ext(spec(prove))]
fun remove_opt_when_absent_spec(x: &mut Foo): Option<Bar> {
    requires(!dof::exists_with_type<u64, Bar>(&x.id, 10));
    let res = remove_opt_when_absent(x);
    ensures(!dof::exists_with_type<u64, Bar>(&x.id, 10));
    ensures(res.is_none());
    res
}

fun remove_opt_when_present(x: &mut Foo): Option<Bar> {
    dof::remove_opt<u64, Bar>(&mut x.id, 10)
}

#[mode(spec), ext(spec(prove))]
fun remove_opt_when_present_spec(x: &mut Foo): Option<Bar> {
    requires(dof::exists_with_type<u64, Bar>(&x.id, 10));
    requires(dof::borrow<u64, Bar>(&x.id, 10).bar == 5);
    let res = remove_opt_when_present(x);
    ensures(!dof::exists_with_type<u64, Bar>(&x.id, 10));
    ensures(res.is_some());
    ensures(res.borrow().bar == 5);
    res
}
