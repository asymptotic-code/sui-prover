module 0x42::issue_416;

use prover::prover::{exists, ensures};
use prover::vector_iter::{map, map_range};

#[ext(pure)]
fun flip(x: &u8): u8 {
    255-*x
}

#[spec_only(loop_inv(target=bar)), ext(pure)]
fun bar_loop_inv(i: u64, stop: u64, v__3: &vector<u8>, v: &vector<u8>, r: &vector<u8>): bool {
    i <= stop && v__3.length() == stop - i && r == map_range!(v, 0, i, |x| flip(x))
        && !exists!(|j| more_loop_inv_3(*j, v, v__3))
}

public fun bar(v: vector<u8>): vector<u8> {
    v.map!(|x| flip(&x))
}

#[spec(prove, boogie_opt=b"vcsMaxKeepGoingSplits:2 vcsSplitOnEveryAssert vcsFinalAssertTimeout:600")]
fun bar_spec(v: vector<u8>): vector<u8> {
    let ans = map!(&v, |x| flip(x));
    let r = bar(v);
    ensures(r == ans);
    r
}

#[ext(pure)]
fun safe_index(v: &vector<u8>, j: u64): u8 {
    if (j < v.length()) { v[j]} else { 0 }
}

#[ext(pure)]
fun more_loop_inv_3(j: u64, v: &vector<u8>, w: &vector<u8>): bool {
    if (j < v.length() && j < w.length() && v.length() <= 100 ) { //(1)
        safe_index(v, v.length() - (j+1)) != safe_index(w, j) // (2)
    } else {
        false
    }
}

// Not Prove but Compile
