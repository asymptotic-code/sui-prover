// borrow_or_unknown returns the element at index `i` if in range, otherwise
// an uninterpreted value. Unlike vector::borrow, it never aborts in specs.

#[allow(unused)]
module 0x42::vector_ext_borrow_or_unknown_ok;

#[spec_only]
use prover::prover::{ensures, requires};

#[spec_only]
use prover::vector_ext::borrow_or_unknown;

// Local method-syntax alias for vector.
#[spec_only]
use fun prover::vector_ext::borrow_or_unknown as vector.borrow_or_unknown;

// In-range: borrow_or_unknown agrees with vector::borrow.
#[spec(prove)]
fun test_in_range_matches_borrow(v: &vector<u64>, i: u64) {
    requires(i < vector::length(v));
    ensures(borrow_or_unknown(v, i) == vector::borrow(v, i));
}

// Method syntax via local `use fun` alias.
#[spec(prove)]
fun test_method_syntax(v: &vector<u64>, i: u64) {
    requires(i < vector::length(v));
    ensures(v.borrow_or_unknown(i) == vector::borrow(v, i));
}

// Concrete value read.
#[spec(prove)]
fun test_concrete_in_range() {
    let v = vector[10u64, 20, 30];
    ensures(*borrow_or_unknown(&v, 0) == 10);
    ensures(*borrow_or_unknown(&v, 1) == 20);
    ensures(*borrow_or_unknown(&v, 2) == 30);
}
