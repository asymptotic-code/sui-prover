// Single-trigger end-step axiom for range_count's is_10 helper
// (test_range_count_specific_value).

axiom (forall start: int, end: int ::
    {$RangeCountQuantifierHelper_$42_quantifiers_range_count_ok_is_10$pure(start, end)}
    start < end ==>
        $RangeCountQuantifierHelper_$42_quantifiers_range_count_ok_is_10$pure(start, end) ==
            $RangeCountQuantifierHelper_$42_quantifiers_range_count_ok_is_10$pure(start, end - 1)
            + (if $42_quantifiers_range_count_ok_is_10$pure(end - 1) then 1 else 0)
);
