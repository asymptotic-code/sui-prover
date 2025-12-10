module 0x42::foo {
    public fun foo(input: u64): u64 {
        assert!(input != 10);

        input
    }
}

module 0x43::bar {
    use prover::prover::asserts;
    use 0x42::foo::foo;

    #[spec(prove)]
    fun scenario_spec(input: u64): u64 {
        asserts(input != 10); // asserts are supported in scenario specs
        let result = foo(input);
        result
    }
}
