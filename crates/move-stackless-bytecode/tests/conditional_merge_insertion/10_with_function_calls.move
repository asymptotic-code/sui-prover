module 0x42::test {
    fun helper(x: u64, y: u64, _z: u8): u64 {
        x + (y as u64)
    }

    public fun f(a: u32): u64 {
        let mut ratio = 1u64;
        let mut temp = 2u64;

        if ((a & 2) != 0) {
            let val = 79236085330515764027303304731u128;
            let shift = 96u8;
            ratio = helper(ratio, (val as u64), shift);
            temp = ratio;
        };

        ratio * temp
    }
}
