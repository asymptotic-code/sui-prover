#[allow(unused_variable, unused_mut_parameter)]
module 0x42::foo;

use prover::prover::{ensures, old};


public struct Foo has key, store {
  id: UID,
}

fun bar(ctx: &mut TxContext) {
}

#[spec(prove)]
fun bar_spec(ctx: &mut TxContext) {
  let old_ctx = old!(ctx);
  bar(ctx);
  let old_ctx_2 = old!(ctx);
  ensures(true);
  let old_ctx_3 = old!(ctx);
}
