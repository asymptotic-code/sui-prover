function {:inline} $42_quantifiers_multiple_args_is_greater_or_equal(a: int, x: int, b: int): bool {
    x >= a && x >= b
}

function {:inline} $42_quantifiers_multiple_args_sum3(x: int, y: int, z: int): int {
    x + y + z
}

function {:inline} $42_quantifiers_multiple_args_all_is_positive(a: int, x: int, b: int): bool {
    a >= 0 && b >= 0 && x >= 0
}