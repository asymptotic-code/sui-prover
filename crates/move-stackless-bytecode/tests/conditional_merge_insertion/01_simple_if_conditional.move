module 0x42::test {
    public fun f(a: u64): u64 {
        let mut result = 0;
        
        if (a > 0) {
            result = result * 10;
        };

        result
    }
}
