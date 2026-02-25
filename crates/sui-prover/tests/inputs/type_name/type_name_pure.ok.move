/// Test that type_name functions can be used as Boogie functions in specs.
/// The type_name functions are marked #[ext(pure)] and called from non-pure
/// functions, which are then verified.
module 0x42::type_name_pure;

use std::type_name;
#[spec_only]
use prover::prover::ensures;

public struct MyCoin has drop {}

#[ext(pure)]
public fun get_type_name(): type_name::TypeName {
    type_name::with_defining_ids<MyCoin>()
}

#[ext(pure)]
public fun get_original_type_name(): type_name::TypeName {
    type_name::with_original_ids<MyCoin>()
}

#[ext(pure)]
public fun get_defining_id(): address {
    type_name::defining_id<MyCoin>()
}

#[ext(pure)]
public fun get_original_id(): address {
    type_name::original_id<MyCoin>()
}

public fun use_type_name(): type_name::TypeName {
    get_type_name()
}

public fun use_original_type_name(): type_name::TypeName {
    get_original_type_name()
}

public fun use_defining_id(): address {
    get_defining_id()
}

public fun use_original_id(): address {
    get_original_id()
}

#[spec(prove)]
fun use_type_name_spec(): type_name::TypeName {
    let result = use_type_name();
    ensures(result == get_type_name());
    result
}

#[spec(prove)]
fun use_original_type_name_spec(): type_name::TypeName {
    let result = use_original_type_name();
    ensures(result == get_original_type_name());
    result
}

#[spec(prove)]
fun use_defining_id_spec(): address {
    let result = use_defining_id();
    ensures(result == get_defining_id());
    result
}

#[spec(prove)]
fun use_original_id_spec(): address {
    let result = use_original_id();
    ensures(result == get_original_id());
    result
}
