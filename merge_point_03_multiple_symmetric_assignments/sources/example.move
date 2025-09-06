module 0x42::my_ssa_test {
    use prover::prover::{ensures};
    #[spec(prove, focus)]
    public fun conditional_max(a: u64, b: u64): u64 {
        let mut r1 = 0;
        let mut r2 = 100;
        
        if (a > b) {
            r1 = a + 10;
            r2 = 25;
        } else {
            r1 = b * 2;
            r2 = r1 * 7;
        };
        
        r1 + r2
    }
}
