// Basic smoke test for prover::prover::split_here. The call emits a
// Boogie `assert {:split_here} true;` which tells Boogie to split the
// verification condition into two smaller VCs at that point.

module 0x42::split_here_simple;

use prover::prover::{ensures, split_here};

#[spec(prove)]
fun split_on_simple_branch(a: u64, b: u64): u64 {
    let r = if (a < b) { a } else { b };
    split_here();
    ensures(r <= a && r <= b);
    r
}
