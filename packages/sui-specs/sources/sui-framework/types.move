module specs::types_spec;

use sui::types::is_one_time_witness;

#[spec(target = sui::types::is_one_time_witness)]
public fun is_one_time_witness_spec<T: drop>(_: &T): bool {
    is_one_time_witness(_)
}
