// Single-trigger end-step axiom for find_indices with is_even in nested_pure.ok.move.
axiom (forall v: Vec (int), start: int, end: int ::
    {$FindIndicesQuantifierHelper_$42_nested_pure_ok_is_even$pure(v, start, end)}
    start < end ==>
    (var res := $FindIndicesQuantifierHelper_$42_nested_pure_ok_is_even$pure(v, start, end);
    (var prev := $FindIndicesQuantifierHelper_$42_nested_pure_ok_is_even$pure(v, start, end - 1);
        (if $42_nested_pure_ok_is_even$pure(ReadVec(v, end - 1)) then
            LenVec(res) == LenVec(prev) + 1 &&
            (forall j: int :: 0 <= j && j < LenVec(prev) ==> ReadVec(res, j) == ReadVec(prev, j)) &&
            ReadVec(res, LenVec(prev)) == end - 1
         else
            LenVec(res) == LenVec(prev) &&
            (forall j: int :: 0 <= j && j < LenVec(prev) ==> ReadVec(res, j) == ReadVec(prev, j)))
    ))
);
