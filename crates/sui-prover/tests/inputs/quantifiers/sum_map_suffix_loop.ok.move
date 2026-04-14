// Loop test with a suffix invariant for `sum_map`. The invariant says:
//
//   s + sum_map_range(v, i, n, f) == sum_map(v, f)
//
// Preserving this across the loop body needs sum_map's start-step axiom:
//   sum_map(v, i, n, f) == f(v[i]) + sum_map(v, i+1, n, f).

module 0x42::sum_map_suffix_loop_ok;

use prover::prover::{ensures, invariant};
use prover::vector_iter::{sum_map, sum_map_range};

// Map to 0 or 1 so the running sum stays bounded and doesn't overflow.
#[ext(pure)]
fun odd_to_int(x: &u64): u64 {
    if ((*x) % 2 == 1) { 1 } else { 0 }
}

fun count_odd_via_sum_suffix(v: &vector<u64>): u64 {
    let mut i = 0;
    let mut s: u64 = 0;
    invariant!(|| ensures(
        i <= v.length()
            && s <= i
            && (s.to_int() + sum_map_range!(v, i, v.length(), |j| odd_to_int(j)))
                == sum_map!(v, |j| odd_to_int(j))
    ));
    while (i < v.length()) {
        s = s + odd_to_int(&v[i]);
        i = i + 1;
    };
    s
}

#[spec(prove)]
fun count_odd_via_sum_suffix_spec(v: &vector<u64>): u64 {
    let r = count_odd_via_sum_suffix(v);
    ensures(r.to_int() == sum_map!(v, |j| odd_to_int(j)));
    r
}
