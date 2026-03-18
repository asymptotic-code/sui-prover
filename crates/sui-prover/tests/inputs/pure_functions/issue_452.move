/// Repro for https://github.com/asymptotic-code/sui-prover/issues/452
/// Panic when a pure function uses `exists!` with enum variant construction.
module 0x42::issue_452;

use prover::prover::ensures;

public enum E has copy, drop {
    A,
    B(u8),
}

#[ext(pure)]
public fun f2(e: E): bool {
    e == E::A || prover::prover::exists!(|v| is_b(*v, e))
}

#[ext(pure)]
public fun is_b(v: u8, e: E): bool {
    e == E::B(v)
}

#[spec(prove)]
fun test() {
    ensures(f2(E::B(1)))
}
