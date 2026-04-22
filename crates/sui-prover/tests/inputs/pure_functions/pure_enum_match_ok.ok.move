module 0x42::pure_enum_match;

#[spec_only]
use prover::prover::ensures;

public enum E has copy, drop {
    A,
    B(u8),
}

#[ext(pure)]
public fun f(e: E): bool {
    match (e) {
        E::A => true,
        E::B(v) => v > 0,
    }
}

#[spec(prove)]
fun test_a() {
    ensures(f(E::A))
}

#[spec(prove)]
fun test_b_one() {
    ensures(f(E::B(1)))
}
