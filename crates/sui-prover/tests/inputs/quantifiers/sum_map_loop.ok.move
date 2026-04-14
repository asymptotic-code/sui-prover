// ensure that a code loop implementing `sum_map` can be proved.

module 0x42::sum_map_loop_ok;

use prover::prover::{ensures, invariant};
use prover::vector_iter::{sum_map, sum_map_range};

// Map each element to 0 or 1, so the running sum stays bounded by the loop index.
#[ext(pure)]
fun odd_to_int(x: &u64): u64 {
    if ((*x) % 2 == 1) { 1 } else { 0 }
}

fun count_odd_via_sum(v: &vector<u64>): u64 {
    let mut i = 0;
    let mut s: u64 = 0;
    invariant!(|| ensures(
        i <= v.length()
            && s <= i
            && s.to_int() == sum_map_range!(v, 0, i, |j| odd_to_int(j))
    ));
    while (i < v.length()) {
        s = s + odd_to_int(&v[i]);
        i = i + 1;
    };
    s
}

#[spec(prove)]
fun count_odd_via_sum_spec(v: &vector<u64>): u64 {
    let r = count_odd_via_sum(v);
    ensures(r.to_int() == sum_map!(v, |j| odd_to_int(j)));
    r
}
