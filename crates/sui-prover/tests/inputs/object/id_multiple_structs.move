module 0x42::object_id_duplicate;

use prover::prover::ensures;

public struct Pool has key, store {
    id: UID,
    value: u64,
}

public struct AnotherPool has key, store {
    id: UID,
    value: u64,
}

public struct YetAnotherPool has key, store {
    id: UID,
    value: u64,
}

// Function that uses the first struct
fun get_pool_id(pool: &Pool): &ID {
    object::id(pool)
}

// Function that uses the second struct
fun get_another_pool_id(pool: &AnotherPool): &ID {
    object::id(pool)
}

// Function that uses the third struct  
fun get_yet_another_pool_id(pool: &YetAnotherPool): &ID {
    object::id(pool)
}

#[spec(prove)]
fun get_pool_uid_spec(pool: &Pool): &ID {
    let r = get_pool_id(pool);
    ensures(r == object::id(pool));
    r
}

#[spec(prove)]
fun get_another_pool_id_spec(pool: &AnotherPool): &ID {
    let r = get_another_pool_id(pool);
    ensures(r == object::id(pool));
    r
}

#[spec(prove)]
fun get_yet_another_pool_id_spec(pool: &YetAnotherPool): &ID {
    let r = get_yet_another_pool_id(pool);
    ensures(r == object::id(pool));
    r
}
