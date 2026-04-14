// Single-trigger end-step axiom for filter's x_is_10 helper.
axiom (forall v: Vec (int), start: int, end: int ::
    {$FilterQuantifierHelper_$42_quantifiers_filter_ok_x_is_10$pure(v, start, end)}
    start < end ==>
    (var res := $FilterQuantifierHelper_$42_quantifiers_filter_ok_x_is_10$pure(v, start, end);
    (var prev := $FilterQuantifierHelper_$42_quantifiers_filter_ok_x_is_10$pure(v, start, end - 1);
        (if $42_quantifiers_filter_ok_x_is_10$pure(ReadVec(v, end - 1)) then
            LenVec(res) == LenVec(prev) + 1 &&
            (forall j: int :: 0 <= j && j < LenVec(prev) ==> ReadVec(res, j) == ReadVec(prev, j)) &&
            ReadVec(res, LenVec(prev)) == ReadVec(v, end - 1)
         else
            LenVec(res) == LenVec(prev) &&
            (forall j: int :: 0 <= j && j < LenVec(prev) ==> ReadVec(res, j) == ReadVec(prev, j)))
    ))
);
