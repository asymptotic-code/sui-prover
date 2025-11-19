module 0x42::test {
    /// Test that sequential if statements don't get incorrectly nested
    /// This pattern is common in bit manipulation code
    fun sequential_if_statements(mut value: u64, flags: u64): u64 {
        if (flags & 0x1 != 0) {
            value = value * 2;
        };
        if (flags & 0x2 != 0) {
            value = value * 3;
        };
        if (flags & 0x4 != 0) {
            value = value * 5;
        };
        if (flags & 0x8 != 0) {
            value = value * 7;
        };
        if (flags & 0x10 != 0) {
            value = value * 11;
        };
        value
    }

    /// Another pattern: sequential if-then-else that should be flat
    fun sequential_if_else(x: u64): u64 {
        let mut result = 0;
        
        if (x == 1) {
            result = 10;
        };
        
        if (x == 2) {
            result = 20;
        };
        
        if (x == 3) {
            result = 30;
        };
        
        result
    }
}
