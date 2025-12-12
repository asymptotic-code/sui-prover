module 0x42::boogie_unknown;

use sui::versioned::{create, Versioned};
public fun bar(ctx: &mut TxContext): Versioned {
    create(0, 1u8, ctx)
}

#[spec(prove)]
public fun bar_spec(ctx: &mut TxContext): Versioned {
    bar(ctx)
}

#[spec_only]
use sui::random::RandomInner;

#[spec]
fun RandomInner_inv(_x: &RandomInner): bool { true }
