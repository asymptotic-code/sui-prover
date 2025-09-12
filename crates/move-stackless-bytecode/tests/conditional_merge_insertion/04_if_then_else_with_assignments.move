module 0x42::ConditionalMergeInsertionTest {
    fun helper_function(a: u128, b: u128, c: u8): u128 {
        (a * b) >> c
    }
    
    fun if_then_else_with_assignments(cond: bool, abs_tick: u32): u128 {
        let mut ratio = if (abs_tick & 0x1 != 0) {
            79232123823359799118286999567u128
        } else {
            79228162514264337593543950336u128
        };
        
        if (cond) {
            let constant = 38992368544603139932233054999993551u128;
            let shift = 96u8;
            ratio = helper_function(ratio, constant, shift);
        };
        
        ratio
    }
}
