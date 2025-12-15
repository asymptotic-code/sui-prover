// ensure that a code loop implementing `map` can be proved.

module 0x42::sum_map_loop_ok;

use prover::prover::{ensures, invariant};
use prover::vector_iter::{sum_map, sum_map_range};

#[ext(pure)]
fun pred(x: u64): u64 {
    if (x == 0) { 0 } else {x - 1}
}

public fun sum_pred(v: &vector<u64>): u64 {
    let mut sum: u64 = 0;
    let mut i = 0;
    invariant!(|| {
        ensures(i <= v.length());
        ensures(sum.to_int() == sum_map_range!(v, 0, i, |x| pred(*x))); }
    ); 
    while (i < v.length()) {
        sum = sum + pred(v[i]);
        i = i+1;
    };
    sum
}

#[spec(prove)]
public fun sum_pred_spec(v: &vector<u64>): u64 {
    requires(sum_map!(v, |x| pred(*x)).lte(std::u64::max_value!().to_int()));
    let r = sum_pred(v);
    ensures(r.to_int() == sum_map!(v, |x| pred(*x)));
    r
}
