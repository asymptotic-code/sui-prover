module 0x42::test {
    public fun f(cond: bool): u64 {
        let mut x = 1;
        let mut y = 2;
        let mut i = 0;

        while (i < 3) {
            if (cond) {
                x = x + 10;  // Increment x in then-block
            } else {
                y = y + 20;  // Increment y in else-block
            };
            i = i + 1;
        };

        x * y
    }
}
