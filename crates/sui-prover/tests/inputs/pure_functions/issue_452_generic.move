// Generic regression for issue 452:
// enum constructor lowering must instantiate fields with the enum operation instantiation.
module 0x42::issue_452_generic;

use prover::prover::ensures;

public enum E<T> has copy, drop {
    A,
    B(T),
}

#[ext(pure)]
public fun wrap_u8(e: E<u8>): bool {
    prover::prover::exists!(|v| matches_b(*v, e))
}

#[ext(pure)]
fun matches_b<T: copy + drop>(v: T, e: E<T>): bool {
    e == E::B(v)
}

#[spec(prove)]
fun test() {
    ensures(wrap_u8(E::B(1)))
}
