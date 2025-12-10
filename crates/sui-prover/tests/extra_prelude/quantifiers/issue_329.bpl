function {:inline} $42_issue_329_some_x_is_10$pure(v: Vec int): bool {
    (exists i:int :: 0 <= i && i < LenVec(v) && $42_issue_329_x_is_10$pure(ReadVec(v, i)))
}
