#[allow(unused)]
module 0x42::quantifiers_funs_non_deterministic_fail;

#[spec_only]
use prover::prover::{forall, ensures};

#[spec_only]
use sui::random::{Random, new_generator, generate_u8_in_range};

#[spec_only, ext(pure)]
fun x_is_gte_0_non_deterministic(x: &u8, r: &Random, ctx: &mut TxContext): bool {
    let mut generator = new_generator(r, ctx); // non-deterministic
    let dice_value = generate_u8_in_range(&mut generator, 1, 6);
    *x + dice_value >= 0
}

#[spec(prove)]
fun test_spec(r: &Random, ctx: &mut TxContext) {
    let positive = forall!<u8>(|x| x_is_gte_0_non_deterministic(x, r, ctx));
    ensures(positive);
}
