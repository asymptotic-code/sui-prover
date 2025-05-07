module 0x42::foo;

use prover::prover::ensures;

use sui::object_table::{Self, ObjectTable};

public struct Foo has key, store {
  id: UID,
}

fun foo(ctx: &mut TxContext): ObjectTable<u64, Foo> {
  object_table::new(ctx)
}

#[spec(prove)]
fun foo_spec(ctx: &mut TxContext): ObjectTable<u64, Foo> {
  let result = foo(ctx);
  ensures(result.is_empty());
  result
}
