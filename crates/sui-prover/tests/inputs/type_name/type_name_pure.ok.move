/// Test that type_name functions can be used as pure functions (Boogie functions).
/// This verifies type_name::get<T>() returns a known constant for concrete types.
module 0x42::type_name_pure;

use std::type_name;
#[spec_only]
use prover::prover::ensures;

public struct MyCoin has drop {}

public fun get_type_name(): type_name::TypeName {
    type_name::get<MyCoin>()
}

#[spec(prove)]
fun get_type_name_spec(): type_name::TypeName {
    let result = get_type_name();
    // type_name::get returns a deterministic value for a given type
    ensures(result == type_name::get<MyCoin>());
    result
}
