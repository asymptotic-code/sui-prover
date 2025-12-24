// ensure that code using vector::map can be proved.

// map is a bit tricky because it consumes the input vector; luckily we can refer to
// the original value in the invariant.  It is also tricky because it reverses that vector,
// then pops values until it has emptied the vector.  The invariant needs to mention the
// relationship between the partly-popped vector (v__3 in the invariant) and the original value
// (v in the invariant).

module 0x42::map_macro_loop_ok;

use prover::prover::{ensures, forall};
use prover::vector_iter::{map, map_range};

#[ext(pure)]
fun flip(x: u64): u64 {
    std::u64::max_value!() - x
}

#[spec_only(loop_inv(target=map_flip)), ext(no_abort)]
fun map_flip_invariant(v: &vector<u64>, v__3: &vector<u64>, i: u64, stop: u64, r: &vector<u64>): bool {
    i <= stop
    && stop - i == v__3.length()
    && r == map_range!(v, 0, i, |e| flip(*e))
    && forall!(|j| more_loop_inv(*j, v, v__3))
}

// v__3 [-j] == w[j] up to the length of v__3
//   (j >= v.length() && j >= w.length())) ==>  v[v.length() - (j+1)] == w[j],
// expressed in a way that we get no aborts
#[ext(pure)]
fun more_loop_inv(j: u64, v: &vector<u64>, w: &vector<u64>): bool {
    j >= v.length()
    || j >= w.length()
    || v[v.length() - (j+1)] == w[j]
}


fun map_flip(v: vector<u64>): vector<u64> {
    v.map!(|x| flip(x))
}

#[spec(prove)]
fun map_flip_spec(v: vector<u64>): vector<u64> {
    let ans = map!(&v, |e| flip(*e));
    let r = map_flip(v);
    ensures(r == ans);
    r
}
