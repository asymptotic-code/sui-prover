module 0x42::issue_102;

use prover::prover::{ensures, requires, invariant};

#[spec_only]
fun fib(n: u16): u16 {
    if (n <= 1) {
        1
    } else {
        fib(n-1) + fib(n-2)
    }
}

fun fib_i(n: u16): u16 {
    if (n <= 1) {
        return 1
    };
    let mut a = 1;
    let mut b = 1;
    let mut i = 2;
    invariant!(|| {ensures (a == fib(i-2) && b == fib(i-1)); } );
    while (i < 10) { // this should depend on n
        let bb = b;
        b = a + b;
        a = bb;
        i = i + 1;
    };
    b
}

#[spec(prove)]
fun fib_i_spec(n: u16): u16 {
    requires(n <= 100);
    let r = fib_i(n);
    ensures(r == fib(n));
    r
}
// should error with recursion error
