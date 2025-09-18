module 0x42::test {
    public fun f(a: u64): u64 {
        let mut x = 1;
        let mut y = 2;

        if (a > 0) {
            x = 99;
            y = 100;
        };

        x * y
    }
}