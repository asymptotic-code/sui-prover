module 0x42::pure_functions_conditionals_rules_fail {
    // This should be invalid - loops
    #[ext(pure)]
    public fun invalid_loop(a: u64): u64 {
        let mut b = a;
        if (b > a) {
            while (b > 0) {
                b = b - a;
            };
        };
        a
    }

    #[spec(focus)]
    public fun test_spec(a: u64) {
        invalid_loop(a);
    }
}
