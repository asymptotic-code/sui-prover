function $42_quantifiers_complex_usage_invariant_expression$pure(j: int, i: int, u: Vec int, v: Vec int): bool {
    LenVec(v) > i && LenVec(u) > j && j <= i && ReadVec(u, j) > ReadVec(v, i)
}
