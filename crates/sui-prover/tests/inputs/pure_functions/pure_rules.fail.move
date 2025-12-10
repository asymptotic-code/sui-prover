module 0x42::pure_functions {
    // This should be valid - simple arithmetic
    #[ext(pure)]
    public fun add(a: u64, b: u64): u64 {
        a + b
    }

    // This should be valid - calls another pure function
    #[ext(pure)]
    public fun add_three(a: u64, b: u64, c: u64): u64 {
        add(a, b) + c
    }

    // This should be invalid - has mutable reference parameter
    #[ext(pure)]
    public fun invalid_mut_ref(v: &mut vector<u64>): u64 {
        vector::length(v)
    }

    // This should be valid - vector::length is native
    #[ext(pure)]
    public fun valid_vector(v: &vector<u64>): u64 {
        vector::length(v)
    }

    // This should be invalid - calls non-pure function
    #[ext(pure)]
    public fun invalid_calls_non_pure(): u64 {
        not_pure()
    }

    // This is not marked as pure, so it's not checked
    public fun not_pure(): u64 {
        42
    }

    // This should be valid - conditionals are allowed
    #[ext(pure)]
    public fun max(a: u64, b: u64): u64 {
        if (a > b) {
            a
        } else {
            b
        }
    }

    // This should be invalid - aborts
    #[ext(pure)]
    public fun invalid_abort(a: u64): u64 {
        assert!(a > 0, 1);
        a
    }

    // This should be invalid - 2 outputs
    #[ext(pure)]
    public fun invalid_two_outputs(a: u64): (u64, u64) {
        (a, a + 1)
    }
}
