// Loop test with a suffix invariant for `range_map`, expressed via concat.
// The invariant
//
//   concat(&r, range_map!(i, n, |k| f(k))) == range_map!(0, n, |k| f(k))
//
// needs range_map's start-step axiom to verify the loop body.

module 0x42::range_map_suffix_loop_ok;

use prover::prover::{ensures, invariant};
use prover::vector_iter::range_map;
use prover::vector_ext::concat;

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
    invariant!(|| ensures(
        i <= n
            && concat(&r, range_map!<u64>(i, n, |k| double(k)))
                == *range_map!<u64>(0, n, |k| double(k))
    ));
    while (i < n) {
        r.push_back(double(i));
        i = i + 1;
    };
    r
}

#[spec(prove)]
fun doubles_up_to_spec(n: u64): vector<u64> {
    let r = doubles_up_to(n);
    ensures(r == *range_map!<u64>(0, n, |k| double(k)));
    r
}
