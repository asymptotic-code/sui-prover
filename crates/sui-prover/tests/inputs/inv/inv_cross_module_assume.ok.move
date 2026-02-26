module 0x42::ext_helper {
    // Returns a u64 guaranteed > 0 by the function logic.
    public fun get_positive(): u64 {
        42
    }
}

module 0x42::inv_cross_module_assume {
    public struct S has copy, drop {
        x: u64
    }

    #[spec_only]
    public fun S_inv(s: &S): bool {
        s.x > 0
    }

    // This function calls a cross-module function and uses the result.
    // Part B wraps cross-module calls with assert-before/assume-after.
    // The returned u64 has no invariant, but this exercises the cross-module
    // call path. The function constructs S with the returned value.
    public fun make_from_external(): S {
        let x = 0x42::ext_helper::get_positive();
        S { x }
    }

    // make_from_external returns S { x: 42 } which satisfies x > 0.
    // The ensures(S_inv(result)) from Part A should pass.
    #[spec(prove)]
    fun make_from_external_spec(): S {
        make_from_external()
    }
}
