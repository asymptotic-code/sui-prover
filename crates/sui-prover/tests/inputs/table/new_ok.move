module 0x42::foo;

use prover::prover::ensures;

use sui::table::{Self, Table};

fun foo(ctx: &mut TxContext): Table<u64, u8> {
  table::new(ctx)
}

#[spec(prove)]
fun foo_spec(ctx: &mut TxContext): Table<u64, u8> {
  let result = foo(ctx);
  ensures(result.is_empty());
  result
}
