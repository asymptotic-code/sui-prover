module 0x42::test {
    public fun f(cond1: bool, cond2: bool): u64 {
        let mut x = 10;
        let mut y = 20;

        if (cond1) {
            x = 99;
            if (cond2) {
                y = 100;
            }
        };

        x * y
    }
}