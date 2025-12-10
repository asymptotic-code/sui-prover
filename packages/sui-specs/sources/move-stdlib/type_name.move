module specs::type_name_spec;

use std::type_name::{TypeName, with_defining_ids, with_original_ids, defining_id, original_id};

#[spec(target = std::type_name::with_defining_ids)]
public fun with_defining_ids_spec<T>(): TypeName {
    with_defining_ids<T>()
}

#[spec(target = std::type_name::with_original_ids)]
public fun with_original_ids_spec<T>(): TypeName {
    with_original_ids<T>()
}

#[spec(target = std::type_name::defining_id)]
public fun defining_id_spec<T>(): address {
    defining_id<T>()
}

#[spec(target = std::type_name::original_id)]
public fun original_id_spec<T>(): address {
    original_id<T>()
}
