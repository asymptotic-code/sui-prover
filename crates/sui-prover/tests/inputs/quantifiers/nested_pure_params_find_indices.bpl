// Single-trigger end-step axiom for find_indices with is_divisible_by in nested_pure_params.ok.move.
axiom (forall v: Vec (int), start: int, end: int, $t1: int ::
    {$FindIndicesQuantifierHelper_$42_nested_pure_ok_is_divisible_by$pure(v, start, end, $t1)}
    start < end ==>
    (var res := $FindIndicesQuantifierHelper_$42_nested_pure_ok_is_divisible_by$pure(v, start, end, $t1);
    (var prev := $FindIndicesQuantifierHelper_$42_nested_pure_ok_is_divisible_by$pure(v, start, end - 1, $t1);
        (if $42_nested_pure_ok_is_divisible_by$pure(ReadVec(v, end - 1), $t1) then
            LenVec(res) == LenVec(prev) + 1 &&
            (forall j: int :: 0 <= j && j < LenVec(prev) ==> ReadVec(res, j) == ReadVec(prev, j)) &&
            ReadVec(res, LenVec(prev)) == end - 1
         else
            LenVec(res) == LenVec(prev) &&
            (forall j: int :: 0 <= j && j < LenVec(prev) ==> ReadVec(res, j) == ReadVec(prev, j)))
    ))
);
