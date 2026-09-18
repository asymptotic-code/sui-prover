module 0x42::tx_context_sender;

use prover::prover::requires;

fun foo(ctx: &TxContext, a: address) {
    assert!(ctx.sender() != a, 1);
}

#[mode(spec), ext(spec(prove))]
fun foo_spec(ctx: &TxContext, a: address) {
    requires(ctx.sender() != a);
    foo(ctx, a);
}
