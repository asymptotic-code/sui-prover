module 0x42::test {
    public fun f(cond: bool): u64 {
        let mut x = 1;
        let mut y = 2;

        if (cond) {
            x = 99;  // Only x is assigned in then-block
        } else {
            y = 100; // Only y is assigned in else-block
        };

        x * y
    }
}