module 0x42::foo;

use sui::versioned::{Self, Versioned};

public struct Validator has store {
    sui_address: address,
}

public struct ValidatorWrapper has store {
    inner: Versioned
}

public fun load_validator(self: &mut ValidatorWrapper): &mut Validator {
    versioned::load_value_mut(&mut self.inner)
}

public fun foo(self: &mut ValidatorWrapper, validator_address: address) {
    let candidate = self.load_validator();
    candidate.sui_address = validator_address;
}

#[spec(target=sui::versioned::load_value_mut)]
public fun load_value_mut_spec<T: store>(self: &mut Versioned): &mut T {
    versioned::load_value_mut(self)
}

#[spec(prove)]
public fun foo_spec(self: &mut ValidatorWrapper, validator_address: address) {
    foo(self, validator_address);
}
