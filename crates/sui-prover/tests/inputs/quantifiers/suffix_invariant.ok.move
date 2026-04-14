// Test with a loop invariant expressed over the *unprocessed suffix* of the
// source vector rather than the processed prefix. This exercises the
// start-recursion direction of the count axiom: preserving
// `c + count(v, i, n) == count(v, 0, n)` across the loop body needs
// `count(v, i, n) == (if p(v[i]) then 1 else 0) + count(v, i+1, n)`.

module 0x42::suffix_invariant_ok;

use prover::prover::{ensures, invariant};
use prover::vector_iter::{count, count_range};

#[ext(pure)]
fun is_odd(x: &u64): bool {
    (*x) % 2 == 1
}

fun count_odd_suffix(v: &vector<u64>): u64 {
    let mut i = 0;
    let mut c = 0;
    invariant!(|| ensures(
        i <= v.length()
            && c <= i
            && (c + count_range!(v, i, v.length(), |j| is_odd(j)))
                == count!(v, |j| is_odd(j))
    ));
    while (i < v.length()) {
        if (is_odd(&v[i])) {
            c = c + 1
        };
        i = i + 1;
    };
    c
}

#[spec(prove)]
fun count_odd_suffix_spec(v: &vector<u64>): u64 {
    let r = count_odd_suffix(v);
    ensures(r == count!(v, |j| is_odd(j)));
    r
}
