// Single-trigger end-step axioms for range_count helpers used by test_range_count.

axiom (forall start: int, end: int ::
    {$RangeCountQuantifierHelper_$42_quantifiers_range_count_ok_is_even$pure(start, end)}
    start < end ==>
        $RangeCountQuantifierHelper_$42_quantifiers_range_count_ok_is_even$pure(start, end) ==
            $RangeCountQuantifierHelper_$42_quantifiers_range_count_ok_is_even$pure(start, end - 1)
            + (if $42_quantifiers_range_count_ok_is_even$pure(end - 1) then 1 else 0)
);

axiom (forall start: int, end: int ::
    {$RangeCountQuantifierHelper_$42_quantifiers_range_count_ok_is_greater_than_5$pure(start, end)}
    start < end ==>
        $RangeCountQuantifierHelper_$42_quantifiers_range_count_ok_is_greater_than_5$pure(start, end) ==
            $RangeCountQuantifierHelper_$42_quantifiers_range_count_ok_is_greater_than_5$pure(start, end - 1)
            + (if $42_quantifiers_range_count_ok_is_greater_than_5$pure(end - 1) then 1 else 0)
);
