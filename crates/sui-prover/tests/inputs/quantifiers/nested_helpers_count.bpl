// Single-trigger end-step axiom for count with is_positive in nested_helpers.
axiom (forall v: Vec (int), start: int, end: int ::
    {$CountQuantifierHelper_$42_quantifiers_nested_helpers_ok_is_positive$pure(v, start, end)}
    start < end ==>
        $CountQuantifierHelper_$42_quantifiers_nested_helpers_ok_is_positive$pure(v, start, end) ==
            $CountQuantifierHelper_$42_quantifiers_nested_helpers_ok_is_positive$pure(v, start, end - 1)
            + (if $42_quantifiers_nested_helpers_ok_is_positive$pure(ReadVec(v, end - 1)) then 1 else 0)
);
