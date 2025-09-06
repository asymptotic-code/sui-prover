module 0x42::my_ssa_test {
    use prover::prover::{ensures};
    #[spec(prove, focus)]
    public fun conditional_max(a: u64, b: u64): u64 {
        let mut result = 0;
        let mut result2 = 0;
        
        if (a > b) {
            result = a; // result_1 = a
        } else {
            result = b; // result_2 = b
        };

				if (a > 0) {
					result2 = result // use of the result of the previous conditional / phi
				} else {
					result2 = a // the original value of 'a'
        };
        // expect this conditional to be a ternary_conditional
        
        result2
    }
}
