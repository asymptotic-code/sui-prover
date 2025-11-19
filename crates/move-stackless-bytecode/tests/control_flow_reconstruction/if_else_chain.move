module 0x42::test {
    fun if_else_if_chain(x: u64): u64 {
        if (x < 10) {
            1
        } else if (x < 20) {
            2
        } else if (x < 30) {
            3
        } else {
            4
        }
    }

    fun nested_if_else(x: u64, y: u64): u64 {
        if (x > 0) {
            if (y > 0) {
                x + y
            } else {
                x - y
            }
        } else {
            if (y > 0) {
                y - x
            } else {
                0
            }
        }
    }
}
