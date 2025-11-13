function {:inline} $42_issue_329_x_is_10(x: int): bool {
    x == 10
}

function {:inline} $42_issue_329_some_x_is_10(v: Vec int): bool {
    (exists i:int :: 0 <= i && i < LenVec(v) && $42_issue_329_x_is_10(ReadVec(v, i)))
}
