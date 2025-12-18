#[allow(unused_variable, unused_mut_parameter)]
module 0x42::foo;

use prover::prover::{ensures, clone};


public struct Foo has key, store {
  id: UID,
}

fun bar(ctx: &mut TxContext) {
}

#[spec(prove)]
fun bar_spec(ctx: &mut TxContext) {
  let old_ctx = clone!(ctx);
  bar(ctx);
  let old_ctx_2 = clone!(ctx);
  ensures(true);
  let old_ctx_3 = clone!(ctx);
}
