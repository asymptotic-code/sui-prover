module 0x42::loop_inv_count_ok;

#[spec_only]
use prover::prover::{invariant, ensures, requires};
#[spec_only]
use prover::vector_iter::{count, count_range};


#[ext(pure)]
fun x_is_positive(x: &u64): bool {
    *x > 0
}

#[spec_only]
fun count_loop(v: &vector<u64>): u64 {
    let mut i = 0;
    let mut r = 0;
    invariant!(|| { 
        ensures(r <= i);
        ensures(i <= v.length());
        ensures(r == count_range!(v, 0, i, |e| x_is_positive(e)));
    });
    while (i < v.length()) {
        if (v[i] > 0) {
            r = r + 1;
        };
        i = i + 1;
    };
    r
}

#[spec(prove)]
fun count_loop_spec(v: &vector<u64>): u64 {
    requires(vector::length(v) == 4);
    requires(*vector::borrow(v, 0) == 10u64);
    requires(*vector::borrow(v, 1) == 0u64);
    requires(*vector::borrow(v, 2) == 5u64);
    requires(*vector::borrow(v, 3) == 20u64);

    let r = count_loop(v);
    ensures(r == count!(v, |e| x_is_positive(e)));
    r
}
