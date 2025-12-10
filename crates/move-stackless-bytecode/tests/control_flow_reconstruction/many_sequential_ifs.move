module 0x42::test {
    /// Test with many sequential if statements like get_sqrt_price_at_positive_tick
    /// This should produce a flat sequence, not nested ifs
    fun many_sequential_ifs(mut ratio: u128, abs_tick: u32): u128 {
        if (abs_tick & 0x1 != 0) {
            ratio = ratio * 2;
        };
        if (abs_tick & 0x2 != 0) {
            ratio = ratio * 3;
        };
        if (abs_tick & 0x4 != 0) {
            ratio = ratio * 5;
        };
        if (abs_tick & 0x8 != 0) {
            ratio = ratio * 7;
        };
        if (abs_tick & 0x10 != 0) {
            ratio = ratio * 11;
        };
        if (abs_tick & 0x20 != 0) {
            ratio = ratio * 13;
        };
        if (abs_tick & 0x40 != 0) {
            ratio = ratio * 17;
        };
        if (abs_tick & 0x80 != 0) {
            ratio = ratio * 19;
        };
        if (abs_tick & 0x100 != 0) {
            ratio = ratio * 23;
        };
        if (abs_tick & 0x200 != 0) {
            ratio = ratio * 29;
        };
        if (abs_tick & 0x400 != 0) {
            ratio = ratio * 31;
        };
        if (abs_tick & 0x800 != 0) {
            ratio = ratio * 37;
        };
        if (abs_tick & 0x1000 != 0) {
            ratio = ratio * 41;
        };
        if (abs_tick & 0x2000 != 0) {
            ratio = ratio * 43;
        };
        if (abs_tick & 0x4000 != 0) {
            ratio = ratio * 47;
        };
        if (abs_tick & 0x8000 != 0) {
            ratio = ratio * 53;
        };
        if (abs_tick & 0x10000 != 0) {
            ratio = ratio * 59;
        };
        if (abs_tick & 0x20000 != 0) {
            ratio = ratio * 61;
        };
        ratio
    }
}
