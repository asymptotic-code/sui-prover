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

    // This should be invalid - nested conditionals not supported yet
    #[ext(pure)]
    public fun invalid_nested_outputs(a: u64): u64 {
        if (a > 0 && a < 100) {
            if (a < 10) {
                a
            } else {
                a + 1
            }
        } else {
            0
        }
    }

    #[spec(focus)]
    public fun test_spec(a: u64) {
        invalid_nested_outputs(a);
        invalid_loop(a);
    }
}
