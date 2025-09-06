module 0x42::my_ssa_test {
    use prover::prover::{ensures};
    #[spec(prove, focus)]
    public fun conditional_max(a: u64, b: u64): u64 {
        let mut result1 = 0;
        let mut result2 = 0;
        let mut result3 = 0;
        
        if (a > b) {
            result1 = a;
            result2 = b;
        } else {
            result2 = a;
            result3 = b
        };
        
        let result = result1 + result2 + result3; 
        result
    }
}
