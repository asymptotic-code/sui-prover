// Single-trigger end-step axiom for filter with is_in_range in nested_pure_params.
axiom (forall v: Vec (int), start: int, end: int, $t1: int, $t2: int ::
    {$FilterQuantifierHelper_$42_nested_pure_ok_is_in_range$pure(v, start, end, $t1, $t2)}
    start < end ==>
    (var res := $FilterQuantifierHelper_$42_nested_pure_ok_is_in_range$pure(v, start, end, $t1, $t2);
    (var prev := $FilterQuantifierHelper_$42_nested_pure_ok_is_in_range$pure(v, start, end - 1, $t1, $t2);
        (if $42_nested_pure_ok_is_in_range$pure(ReadVec(v, end - 1), $t1, $t2) then
            LenVec(res) == LenVec(prev) + 1 &&
            (forall j: int :: 0 <= j && j < LenVec(prev) ==> ReadVec(res, j) == ReadVec(prev, j)) &&
            ReadVec(res, LenVec(prev)) == ReadVec(v, end - 1)
         else
            LenVec(res) == LenVec(prev) &&
            (forall j: int :: 0 <= j && j < LenVec(prev) ==> ReadVec(res, j) == ReadVec(prev, j)))
    ))
);
