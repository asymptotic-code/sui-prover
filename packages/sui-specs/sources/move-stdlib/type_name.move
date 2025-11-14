module specs::type_name_spec;

use std::type_name::{TypeName, get, with_original_ids};

#[spec(target = std::type_name::get)]
public fun get_spec<T>(): TypeName {
    get<T>()
}

#[spec(target = std::type_name::with_original_ids)]
public fun with_original_ids_spec<T>(): TypeName {
    with_original_ids<T>()
}
