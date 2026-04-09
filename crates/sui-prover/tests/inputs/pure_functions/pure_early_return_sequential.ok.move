/// Test that multiple sequential early returns in pure functions work correctly.
/// Each condition is checked in order; the first match returns.
module 0x42::pure_early_return_sequential;

#[spec_only]
use prover::prover::ensures;

#[ext(pure)]
fun bucket(x: u64): u64 {
    if (x < 10) { return 1 };
    if (x < 20) { return 2 };
    if (x < 30) { return 3 };
    if (x < 40) { return 4 };
    5
}

public fun call_bucket(x: u64): u64 {
    bucket(x)
}

#[spec(prove)]
fun test_bucket_1(): u64 {
    let r = call_bucket(5);
    ensures(r == 1);
    r
}

#[spec(prove)]
fun test_bucket_2(): u64 {
    let r = call_bucket(15);
    ensures(r == 2);
    r
}

#[spec(prove)]
fun test_bucket_3(): u64 {
    let r = call_bucket(25);
    ensures(r == 3);
    r
}

#[spec(prove)]
fun test_bucket_4(): u64 {
    let r = call_bucket(35);
    ensures(r == 4);
    r
}

#[spec(prove)]
fun test_bucket_5(): u64 {
    let r = call_bucket(99);
    ensures(r == 5);
    r
}
