// Loop test with a suffix invariant for `map`, expressed via concat. The
// invariant
//
//   append_pure(r, map_range(v, i, n)) == map(v, f)
//
// needs the start-step direction of map's recursive axiom to verify the body.

module 0x42::map_suffix_loop_ok;

use prover::prover::{ensures, invariant};
use prover::vector_iter::{map, map_range};
use prover::vector_ext::append_pure;

#[ext(pure)]
fun double(x: &u64): u64 {
    if (*x > std::u64::max_value!() / 2) {
        std::u64::max_value!()
    } else {
        *x * 2
    }
}

fun map_doubles(v: &vector<u64>): vector<u64> {
    let n = vector::length(v);
    let mut i = 0;
    let mut r = vector[];
    invariant!(|| ensures(
        i <= n
            && append_pure(&r, map_range!(v, i, n, |x| double(x))) == *map!(v, |x| double(x))
    ));
    while (i < n) {
        r.push_back(double(vector::borrow(v, i)));
        i = i + 1;
    };
    r
}

#[spec(prove)]
fun map_doubles_spec(v: &vector<u64>): vector<u64> {
    let r = map_doubles(v);
    ensures(r == *map!(v, |x| double(x)));
    r
}
