// ensure that a code loop implementing `map` can be proved.

module 0x42::map_loop_ok;

use prover::prover::{ensures, invariant};
use prover::vector_iter::{map, map_range};

#[ext(pure)]
fun pred(x: u64): u64 {
    if (x == 0) { 0 } else {x - 1}
}

fun map_pred(v: &vector<u64>): vector<u64> {
    let mut i = 0;
    let mut r = vector[];
    invariant!(|| ensures(i <= v.length() && r == map_range!(v, 0, i, |e| pred(*e))));
    while (i < v.length()) {
        r.push_back(pred(v[i]));
        i = i + 1;
    };
    r
}

#[spec(prove)]
fun map_pred_spec(v: &vector<u64>): vector<u64> {
    let r = map_pred(v);
    ensures(r == map!(v, |j| pred(*j)));
    r
}
