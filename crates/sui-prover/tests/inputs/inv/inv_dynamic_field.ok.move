module 0x42::inv_dynamic_field;

use sui::dynamic_field;

public struct Vault has key {
    id: UID,
    balance: u64,
}

// Invariant: balance must be positive.
#[spec_only]
public fun Vault_inv(v: &Vault): bool {
    v.balance > 0
}

// Creates a valid vault (balance=100) and adds a dynamic field.
// The dynamic_field::add call takes &mut Vault as argument after
// DynamicFieldAnalysis rewriting, so Part B asserts Vault_inv before
// the cross-module call. Vault_inv holds because balance=100.
public fun make_good(ctx: &mut TxContext): Vault {
    let mut v = Vault { id: object::new(ctx), balance: 100 };
    dynamic_field::add<u8, u64>(&mut v.id, 0, 42);
    v
}

// Creates an INVALID vault (balance=0) and tries to add a dynamic field.
// The cross-module dynamic_field::add call triggers Part B assert on the
// Vault argument, catching the invariant violation at the call site.
public fun make_bad(ctx: &mut TxContext): Vault {
    let mut v = Vault { id: object::new(ctx), balance: 0 };
    dynamic_field::add<u8, u64>(&mut v.id, 0, 42);
    v
}

// Sets balance to 0 via mut ref, violating the invariant ensures.
public fun drain(v: &mut Vault) {
    v.balance = 0;
}

// Should pass: make_good creates a valid Vault.
#[spec(prove)]
fun make_good_spec(ctx: &mut TxContext): Vault {
    make_good(ctx)
}

// Should fail: make_bad creates invalid Vault, caught at dynamic_field::add.
#[spec(prove)]
fun make_bad_spec(ctx: &mut TxContext): Vault {
    make_bad(ctx)
}

// Should fail: drain sets balance=0, ensures fails on mut ref.
#[spec(prove)]
fun drain_spec(v: &mut Vault) {
    drain(v)
}
