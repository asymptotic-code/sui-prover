// Basic smoke test for prover::prover::boogie_split_here. The call emits
// a Boogie `assume {:split_here} true;` which tells Boogie to split the
// verification condition into two smaller VCs at that point.

module 0x42::split_here_simple;

use prover::prover::{ensures, boogie_split_here};

#[spec(prove)]
fun split_on_simple_branch(a: u64, b: u64): u64 {
    let r = if (a < b) { a } else { b };
    boogie_split_here();
    ensures(r <= a && r <= b);
    r
}
