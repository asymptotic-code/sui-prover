module 0x42::loop_invariant_issue_466;

use prover::prover::ensures;

public struct T {
    x: vector<u8>,
    y: u64,
}

fun f2(t: &mut T): u64 {
    let length = t.x.length();
    let mut i = 0;
    while (i < length) {
        i = i + 1;
        t.y = i;
    };
    t.x.length()
}

#[spec_only(loop_inv(target = f2)), ext(pure)]
fun f2_invariant(i: u64, length: u64, t: &T, __old_t: &T): bool {
    t.x == __old_t.x
}

#[spec(prove)]
fun f2_spec(t: &mut T): u64 {
    let r = f2(t);
    ensures(r >= 0);
    r
}
