module 0x42::asserts_loop_nested_fail;

use prover::prover::{ensures, asserts, invariant};

// Nested loops where both bodies have per-iteration assertions tied
// to function-level asserts. The Assume direction fails for the inner
// loop's asserts because the prover does not propagate the inner
// invariant's contradiction at loop exit (`j == m && j <= 200` with
// `m > 200`) outward to conclude that the surrounding function aborts.
//
// The same pattern works when the loops are sequential rather than
// nested — see `asserts_loop_sequential.move`.

fun nested(n: u64, m: u64) {
    let mut i: u64 = 0;
    invariant!(|| {
        ensures(i <= n);
        ensures(i <= 100);
    });
    while (i < n) {
        assert!(i < 100);
        let mut j: u64 = 0;
        invariant!(|| {
            ensures(j <= m);
            ensures(j <= 200);
        });
        while (j < m) {
            assert!(j < 200);
            j = j + 1;
        };
        i = i + 1;
    };
}

#[spec(prove)]
fun nested_spec(n: u64, m: u64) {
    asserts(n <= 100 && (n == 0 || m <= 200));
    nested(n, m);
}
