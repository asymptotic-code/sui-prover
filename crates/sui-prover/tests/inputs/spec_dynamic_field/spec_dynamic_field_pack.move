module 0x42::foo_spec;
use sui::dynamic_field;

public struct Versioned has key, store {
    id: UID,
    version: u64,
}

public fun create<T: store>(init_version: u64, init_value: T, ctx: &mut TxContext): Versioned {
    let mut self = Versioned {
        id: object::new(ctx),
        version: init_version,
    };
    dynamic_field::add(&mut self.id, init_version, init_value);
    self
}

#[spec(prove)]
public fun create_spec<T: store>(init_version: u64, init_value: T, ctx: &mut TxContext): Versioned {
    create(init_version, init_value, ctx)
}