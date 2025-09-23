module 0x42::test {
    public fun f(a: u64): u64 {
        let mut x = 10;
        let y;
        
        if (a > 0) {
            y = 30;
        } else {
            x = 20;
            y = 40;
        };

        x * y
    }
}
