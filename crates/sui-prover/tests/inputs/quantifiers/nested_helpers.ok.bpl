// Single-trigger end-step axiom for nested_helpers' is_even filter helper.
axiom (forall v: Vec (int), start: int, end: int ::
    {$FilterQuantifierHelper_$42_quantifiers_nested_helpers_ok_is_even$pure(v, start, end)}
    start < end ==>
    (var res := $FilterQuantifierHelper_$42_quantifiers_nested_helpers_ok_is_even$pure(v, start, end);
    (var prev := $FilterQuantifierHelper_$42_quantifiers_nested_helpers_ok_is_even$pure(v, start, end - 1);
        (if $42_quantifiers_nested_helpers_ok_is_even$pure(ReadVec(v, end - 1)) then
            LenVec(res) == LenVec(prev) + 1 &&
            (forall j: int :: 0 <= j && j < LenVec(prev) ==> ReadVec(res, j) == ReadVec(prev, j)) &&
            ReadVec(res, LenVec(prev)) == ReadVec(v, end - 1)
         else
            LenVec(res) == LenVec(prev) &&
            (forall j: int :: 0 <= j && j < LenVec(prev) ==> ReadVec(res, j) == ReadVec(prev, j)))
    ))
);
