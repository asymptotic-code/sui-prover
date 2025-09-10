module specs::type_name_spec;

use std::type_name::{TypeName, get, get_with_original_ids};

#[spec(target = std::type_name::get)]
public fun get_spec<T>(): TypeName {
    get<T>()
}

#[spec(target = std::type_name::get_with_original_ids)]
public fun get_with_original_ids_spec<T>(): TypeName {
    get_with_original_ids<T>()
}
