module 0x42::my_ssa_test {
    use prover::prover::{ensures};
    #[spec(prove, focus)]
    public fun conditional_max(score: u64): u8 {
        let mut grade;

        if (score >= 90) {
            grade = 1u8;  // A
        } else {
            if (score >= 70) {
                grade = 2u8;  // B
            } else {
                grade = 3u8;  // C
            }
        };

        grade
    }
}
