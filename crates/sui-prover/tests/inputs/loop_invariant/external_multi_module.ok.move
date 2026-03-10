// Two modules provide a loop invariant for the same spec function.
// The invariant in the same module as the spec should be selected.
module 0x42::other_specs {
    #[allow(unused_variable)]
    #[spec_only(loop_inv(target = 0x42::my_specs::test_spec))]
    #[ext(no_abort)]
    fun loop_inv_other(i: u64, n: u64): bool {
        // This invariant is intentionally too weak; it would fail if selected.
        true
    }
}

module 0x42::my_specs {
    use prover::prover::ensures;

    #[spec_only(loop_inv(target = test_spec))]
    #[ext(no_abort)]
    fun loop_inv(i: u64, n: u64): bool {
        i <= n
    }

    #[spec(prove)]
    fun test_spec(n: u64) {
        let mut i = 0;

        while (i < n) {
            i = i + 1;
        };

        ensures(i == n);
    }
}
