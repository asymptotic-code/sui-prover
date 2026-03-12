module 0x42::inv_dynamic_field_in_inv;

use sui::dynamic_field;

public struct Vault has key {
    id: UID,
}

// Invariant uses dynamic_field::exists_with_type inside the inv function.
// This requires the DynamicFieldAnalysis to include invariant functions
// when collecting dynamic field info for the Boogie backend.
#[spec_only]
public fun Vault_inv(v: &Vault): bool {
    dynamic_field::exists_with_type<u8, u64>(&v.id, 0)
}

// Takes a vault that has the required dynamic field, reads from it.
// Part A adds requires(Vault_inv(v)) and ensures on return — should pass.
public fun read_balance(v: &Vault): u64 {
    *dynamic_field::borrow<u8, u64>(&v.id, 0)
}

// Creates a vault WITHOUT the required dynamic field — violates invariant.
public fun make_bad(ctx: &mut TxContext): Vault {
    Vault { id: object::new(ctx) }
}

// Should pass: read_balance takes a valid vault (requires ensures inv holds).
#[spec(prove)]
fun read_balance_spec(v: &Vault): u64 {
    read_balance(v)
}

// Should fail: make_bad returns a vault missing the dynamic field.
#[spec(prove)]
fun make_bad_spec(ctx: &mut TxContext): Vault {
    make_bad(ctx)
}
