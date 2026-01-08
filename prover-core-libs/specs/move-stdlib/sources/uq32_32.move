module std::uq32_32_spec {
    use std::uq32_32;
    use std::uq32_32::UQ32_32;

    #[spec(prove)]
    fun from_quotient_spec(numerator: u64, denominator: u64): UQ32_32 {
        let result = uq32_32::from_quotient(numerator, denominator);
        result
    }

    #[spec(prove)]
    fun from_int_spec(integer: u32): UQ32_32 {
        let result = uq32_32::from_int(integer);
        result
    }

    #[spec(prove)]
    fun add_spec(a: UQ32_32, b: UQ32_32): UQ32_32 {
        let result = uq32_32::add(a, b);
        result
    }

    #[spec(prove)]
    fun sub_spec(a: UQ32_32, b: UQ32_32): UQ32_32 {
        let result = uq32_32::sub(a, b);
        result
    }

    #[spec(prove)]
    fun mul_spec(a: UQ32_32, b: UQ32_32): UQ32_32 {
        let result = uq32_32::mul(a, b);
        result
    }

    #[spec(prove)]
    fun div_spec(a: UQ32_32, b: UQ32_32): UQ32_32 {
        let result = uq32_32::div(a, b);
        result
    }

    #[spec(prove)]
    fun to_int_spec(a: UQ32_32): u32 {
        let result = uq32_32::to_int(a);
        result
    }

    #[spec(prove)]
    fun int_mul_spec(val: u64, multiplier: UQ32_32): u64 {
        let result = uq32_32::int_mul(val, multiplier);
        result
    }

    #[spec(prove)]
    fun int_div_spec(val: u64, divisor: UQ32_32): u64 {
        let result = uq32_32::int_div(val, divisor);
        result
    }

    #[spec(prove)]
    fun le_spec(a: UQ32_32, b: UQ32_32): bool {
        let result = uq32_32::le(a, b);
        result
    }

    #[spec(prove)]
    fun lt_spec(a: UQ32_32, b: UQ32_32): bool {
        let result = uq32_32::lt(a, b);
        result
    }

    #[spec(prove)]
    fun ge_spec(a: UQ32_32, b: UQ32_32): bool {
        let result = uq32_32::ge(a, b);
        result
    }

    #[spec(prove)]
    fun gt_spec(a: UQ32_32, b: UQ32_32): bool {
        let result = uq32_32::gt(a, b);
        result
    }

    #[spec(prove)]
    fun to_raw_spec(a: UQ32_32): u64 {
        let result = uq32_32::to_raw(a);
        result
    }

    #[spec(prove)]
    fun from_raw_spec(raw_value: u64): UQ32_32 {
        let result = uq32_32::from_raw(raw_value);
        result
    }
}
