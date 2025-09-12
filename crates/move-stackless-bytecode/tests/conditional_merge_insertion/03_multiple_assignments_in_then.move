module 0x42::ConditionalMergeInsertionTest {
    fun multiple_assignments_in_then(cond: bool, input: u128): u128 {
        let mut ratio = input;
        if (cond) {
            let constant = 38992368544603139932233054999993551u128;
            let shift = 96u8;
            let intermediate = ratio * constant;
            ratio = intermediate >> shift;
        };
        ratio
    }
}