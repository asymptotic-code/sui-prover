module 0x42::test {
    fun simple_if(x: u64): u64 {
        let result = if (x > 10) {
            x + 1
        } else {
            x - 1
        };
        result
    }

    fun if_then_only(mut x: u64): u64 {
        if (x > 5) {
            x = x * 2;
        };
        x
    }
}
