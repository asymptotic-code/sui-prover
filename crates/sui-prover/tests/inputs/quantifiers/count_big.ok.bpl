// Single-trigger end-step axioms for count_big's per-predicate helpers.

axiom (forall v: Vec (int), start: int, end: int ::
    {$CountQuantifierHelper_$42_quantifiers_count_big_ok_is_even$pure(v, start, end)}
    start < end ==>
        $CountQuantifierHelper_$42_quantifiers_count_big_ok_is_even$pure(v, start, end) ==
            $CountQuantifierHelper_$42_quantifiers_count_big_ok_is_even$pure(v, start, end - 1)
            + (if $42_quantifiers_count_big_ok_is_even$pure(ReadVec(v, end - 1)) then 1 else 0)
);

axiom (forall v: Vec (int), start: int, end: int ::
    {$CountQuantifierHelper_$42_quantifiers_count_big_ok_is_positive$pure(v, start, end)}
    start < end ==>
        $CountQuantifierHelper_$42_quantifiers_count_big_ok_is_positive$pure(v, start, end) ==
            $CountQuantifierHelper_$42_quantifiers_count_big_ok_is_positive$pure(v, start, end - 1)
            + (if $42_quantifiers_count_big_ok_is_positive$pure(ReadVec(v, end - 1)) then 1 else 0)
);
