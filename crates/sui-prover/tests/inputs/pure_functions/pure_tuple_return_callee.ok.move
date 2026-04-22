/// Test that `#[ext(pure)]` helpers can destructure multi-destination
/// operations: tuple-returning function calls and struct unpacks.
/// Previously the Boogie backend panicked in `generate_pure_expression`
/// on any `Call` with `dests.len() > 1`.
module 0x42::pure_tuple_return_callee;

#[spec_only]
use prover::prover::ensures;

// --- Tuple return -----------------------------------------------------------

fun split(x: u64): (u64, u64) {
    if (x >= 2) {
        (1, x - 1)
    } else {
        (0, x)
    }
}

#[ext(pure)]
fun pure_sum_parts(x: u64): u64 {
    let (a, b) = split(x);
    a + b
}

#[ext(pure)]
fun pure_second(x: u64): u64 {
    let (_, b) = split(x);
    b
}

public fun call_through_sum(x: u64): u64 {
    pure_sum_parts(x)
}

public fun call_through_second(x: u64): u64 {
    pure_second(x)
}

#[spec(prove)]
fun verify_sum_helper(): u64 {
    let result = call_through_sum(5);
    ensures(result == 5);
    result
}

#[spec(prove)]
fun verify_second_helper(): u64 {
    let result = call_through_second(5);
    ensures(result == 4);
    result
}

// --- Struct unpack ----------------------------------------------------------

public struct Pair has copy, drop { left: u64, right: u64 }

fun make_pair(x: u64): Pair {
    if (x >= 10) {
        Pair { left: 0, right: x - 1 }
    } else {
        Pair { left: x, right: x + 1 }
    }
}

#[ext(pure)]
fun pure_pair_sum(x: u64): u64 {
    let Pair { left, right } = make_pair(x);
    left + right
}

public fun call_through_pair_sum(x: u64): u64 {
    pure_pair_sum(x)
}

#[spec(prove)]
fun verify_pair_sum_helper(): u64 {
    let result = call_through_pair_sum(3);
    ensures(result == 7);
    result
}

// --- Three-element tuple ----------------------------------------------------

fun triple(x: u64): (u64, u64, u64) {
    if (x >= 4) {
        (1, 2, x - 3)
    } else {
        (0, 0, x)
    }
}

#[ext(pure)]
fun pure_triple_sum(x: u64): u64 {
    let (a, b, c) = triple(x);
    a + b + c
}

public fun call_through_triple_sum(x: u64): u64 {
    pure_triple_sum(x)
}

#[spec(prove)]
fun verify_triple_sum_helper(): u64 {
    let result = call_through_triple_sum(7);
    ensures(result == 7);
    result
}
