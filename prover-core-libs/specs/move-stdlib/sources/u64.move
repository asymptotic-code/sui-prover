module std::u64_spec {
    use std::u64;
    use std::string::String;

    #[spec(prove)]
    fun bitwise_not_spec(x: u64): u64 {
        let result = u64::bitwise_not(x);
        result
    }

    #[spec(prove)]
    fun max_spec(x: u64, y: u64): u64 {
        let result = u64::max(x, y);
        result
    }

    #[spec(prove)]
    fun min_spec(x: u64, y: u64): u64 {
        let result = u64::min(x, y);
        result
    }

    #[spec(prove)]
    fun diff_spec(x: u64, y: u64): u64 {
        let result = u64::diff(x, y);
        result
    }

    #[spec(prove)]
    fun divide_and_round_up_spec(x: u64, y: u64): u64 {
        let result = u64::divide_and_round_up(x, y);
        result
    }

    #[spec(prove)]
    fun pow_spec(base: u64, exponent: u8): u64 {
        let result = u64::pow(base, exponent);
        result
    }

    #[spec(prove)]
    fun sqrt_spec(x: u64): u64 {
        let result = u64::sqrt(x);
        result
    }

    #[spec(prove)]
    fun try_as_u8_spec(x: u64): Option<u8> {
        let result = u64::try_as_u8(x);
        result
    }

    #[spec(prove)]
    fun try_as_u16_spec(x: u64): Option<u16> {
        let result = u64::try_as_u16(x);
        result
    }

    #[spec(prove)]
    fun try_as_u32_spec(x: u64): Option<u32> {
        let result = u64::try_as_u32(x);
        result
    }

    #[spec(prove)]
    fun to_string_spec(x: u64): String {
        let result = u64::to_string(x);
        result
    }
}
