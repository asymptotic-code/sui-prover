module 0x42::foo;

use sui::dynamic_field;

public struct Versioned has key, store {
    id: UID,
    version: u64,
}

public struct Validator has store {
    sui_address: address,
}

public struct ValidatorWrapper has store {
    inner: Versioned
}

public fun borrow_mut<T: store>(id: &mut UID, version: u64): &mut T {
    dynamic_field::borrow_mut(id, version)
}

public fun load_value_mut<T: store>(self: &mut Versioned): &mut T {
    borrow_mut(&mut self.id, self.version)
}

public fun load_validator(self: &mut ValidatorWrapper): &mut Validator {
    load_value_mut(&mut self.inner)
}

public fun foo(self: &mut ValidatorWrapper, validator_address: address) {
    let candidate = self.load_validator();
    candidate.sui_address = validator_address;
}

#[spec]
public fun load_value_mut_spec<T: store>(self: &mut Versioned): &mut T {
    load_value_mut(self)
}

#[spec(prove)]
public fun foo_spec(self: &mut ValidatorWrapper, validator_address: address) {
    foo(self, validator_address);
}
