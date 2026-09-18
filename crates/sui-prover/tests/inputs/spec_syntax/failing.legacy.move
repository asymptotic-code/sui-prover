// Parameters that make verification fail, in the deprecated syntax; the failures must
// match failing.new.move exactly.
module 0x42::failing;

#[spec_only]
use prover::prover::ensures;

public struct Counter has drop { value: u64 }

#[spec_only]
fun Counter_inv(c: &Counter): bool { c.value <= 100 }

public fun overflow(c: &mut Counter) {
    c.value = 500;
}

#[ext(pure)]
public fun id(x: u64): u64 { x }

public fun use_id(x: u64): u64 { id(x) }

public fun count(x: u8) {
    let mut y = 0;
    while (y < x) {
        y = y + 1;
    }
}

#[spec_only(loop_inv(target = count)), ext(pure)]
fun count_inv(y: u8, x: u8): bool {
    y < x
}

// Breaks the Counter invariant.
#[spec(prove)]
fun overflow_spec(c: &mut Counter) {
    overflow(c);
}

// `id` is uninterpreted here, so its result is unknown.
#[spec(prove, uninterpreted = id)]
fun use_id_spec(x: u64): u64 {
    let r = use_id(x);
    ensures(r == x);
    r
}

// The loop invariant does not hold on exit.
#[spec(prove)]
fun count_spec(x: u8) {
    count(x)
}
