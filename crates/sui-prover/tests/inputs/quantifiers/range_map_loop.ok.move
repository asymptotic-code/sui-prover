// ensure that a code loop implementing `range_map` can be proved.

module 0x42::range_map_loop_ok;

use prover::prover::{ensures, invariant};
use prover::vector_iter::range_map;

#[ext(pure)]
fun double(x: u64): u64 {
    if (x > std::u64::max_value!() / 2) {
        std::u64::max_value!()
    } else {
        x * 2
    }
}

fun doubles_up_to(n: u64): vector<u64> {
    let mut i = 0;
    let mut r = vector[];
    invariant!(|| ensures(i <= n && r == range_map!<u64>(0, i, |k| double(k))));
    while (i < n) {
        r.push_back(double(i));
        i = i + 1;
    };
    r
}

#[spec(prove)]
fun doubles_up_to_spec(n: u64): vector<u64> {
    let r = doubles_up_to(n);
    ensures(r == range_map!<u64>(0, n, |k| double(k)));
    r
}
