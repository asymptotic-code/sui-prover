// `include` and `extra_bpl` on modules and functions, in the deprecated syntax.
// includes.new.move is the same file in the new syntax; outputs must match.
module 0x42::fb {
    native fun foo();

    public fun bar() {
        foo();
    }
}

module 0x42::foo_specs {
    use prover::prover::ensures;
    use 0x42::fb::foo;

    #[spec(prove, target = 0x42::fb::foo)]
    public fun foo_spec() {
        foo();
        ensures(true);
    }
}

// Including foo_spec replaces the unimplemented native `foo` when proving `bar`.
#[spec_only(include = 0x42::foo_specs::foo_spec, extra_bpl = b"includes.module.bpl")]
module 0x42::bar_specs {
    use prover::prover::ensures;
    use 0x42::fb::bar;

    // Defined in includes.module.bpl.
    #[spec_only]
    native fun triple(x: u64): u64;

    // Defined in includes.fn_a.bpl and includes.fn_b.bpl.
    #[spec_only]
    native fun plus_one(x: u64): u64;

    #[spec_only]
    native fun minus_one(x: u64): u64;

    #[spec(prove, target = 0x42::fb::bar, extra_bpl = b"includes.fn_a.bpl", extra_bpl = b"includes.fn_b.bpl")]
    public fun bar_spec() {
        bar();
        ensures(triple(2) == 6);
        ensures(plus_one(2) == 3);
        ensures(minus_one(2) == 1);
    }
}
