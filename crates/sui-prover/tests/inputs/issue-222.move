module 0x42::foo;

use sui::table::Table;
use sui::versioned::Versioned;

use prover::prover::requires;

public struct Validator has store {
    sui_address: address,
}

public struct ValidatorSet has store {
    staking_pool_mappings: Table<ID, address>,
    inactive_validators: Table<ID, Versioned>,
}

public fun foo(self: &mut ValidatorSet, pool_id: &ID): address {
    // If the pool id is recorded in the mapping, then it must be either candidate or active.
    if (self.staking_pool_mappings.contains(*pool_id)) {
        self.staking_pool_mappings[*pool_id]
    } else {
        let wrapper = &mut self.inactive_validators[*pool_id];
        let validator = wrapper.load_value_mut<Validator>();
        validator.sui_address
    }
}

#[spec(prove)]
public fun foo_spec(self: &mut ValidatorSet, pool_id: &ID): address {
    requires(
        self.staking_pool_mappings.contains(*pool_id) || self.inactive_validators.contains(*pool_id),
    );
    foo(self, pool_id)
}
