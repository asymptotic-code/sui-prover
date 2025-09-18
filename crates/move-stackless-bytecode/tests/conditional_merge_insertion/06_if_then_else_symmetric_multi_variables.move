module 0x42::test {
    public fun f(a: u64): u64 {
        let x;
        let y;
        
        if (a > 0) {
            x = 10;
            y = 30;
        } else {
            x = 20;
            y = 40;
        };

        x * y
    }
}
