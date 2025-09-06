module 0x42::my_ssa_test {
    use prover::prover::{ensures};
    #[spec(prove, focus)]
    public fun conditional_max(a: u64, b: u64): u64 {
        let mut result = 7;
        
        if (a > b) {
            result = 42;
        };
        
        result
    }
}
