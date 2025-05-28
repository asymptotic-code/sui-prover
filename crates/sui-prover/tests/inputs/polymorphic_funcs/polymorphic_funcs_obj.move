module 0x42::foo;

#[spec_only]
use prover::prover::ensures;

public struct EmptyObj has key {
    id: UID,
}

public struct TestObj has key, store {
    id: UID,
    value: u64,
}

public struct Test2Obj has key, store {
    id: UID,
    value: u8,
}

public fun get_id<T: key>(obj: &T): object::ID {
    object::id(obj)
}

#[spec(prove, target = get_id)]
fun get_id_empty_spec(
    obj: &EmptyObj,
): object::ID {
    let id = get_id(obj);
    ensures(true);
    id
}

#[spec(prove, target = get_id)]
fun get_id_test_spec(
    obj: &TestObj,
): object::ID {
    let id = get_id(obj);
    ensures(true);
    id
}

#[spec(prove, target = get_id)]
fun get_id_test2_spec(
    obj: &Test2Obj,
): object::ID {
    let id = get_id(obj);
    ensures(true);
    id
}
