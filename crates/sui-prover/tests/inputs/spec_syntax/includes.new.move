// `include` and `extra_bpl` on modules and functions, in the new syntax.
// includes.legacy.move is the same file in the deprecated syntax.
module 0x42::fb {
    native fun foo();

    public fun bar() {
        foo();
    }
}

module 0x42::foo_specs {
    use prover::prover::ensures;
    use 0x42::fb::foo;

    #[mode(spec), ext(spec(prove, target = 0x42::fb::foo))]
    public fun foo_spec() {
        foo();
        ensures(true);
    }
}

// Including foo_spec replaces the unimplemented native `foo` when proving `bar`.
#[mode(spec), ext(spec_only(include = 0x42::foo_specs::foo_spec, extra_bpl = b"includes.module.bpl"))]
module 0x42::bar_specs {
    use prover::prover::ensures;
    use 0x42::fb::bar;

    // Defined in includes.module.bpl.
    #[mode(spec), ext(spec_only)]
    native fun triple(x: u64): u64;

    // Defined in includes.fn_a.bpl and includes.fn_b.bpl.
    #[mode(spec), ext(spec_only)]
    native fun plus_one(x: u64): u64;

    #[mode(spec), ext(spec_only)]
    native fun minus_one(x: u64): u64;

    #[mode(spec), ext(spec(prove, target = 0x42::fb::bar, extra_bpl(a = b"includes.fn_a.bpl", b = b"includes.fn_b.bpl")))]
    public fun bar_spec() {
        bar();
        ensures(triple(2) == 6);
        ensures(plus_one(2) == 3);
        ensures(minus_one(2) == 1);
    }
}
