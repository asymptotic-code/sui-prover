// Single-trigger end-step axiom for range_count's is_even helper
// in range_count_pure.ok.move.

axiom (forall start: int, end: int ::
    {$RangeCountQuantifierHelper_$42_quantifiers_range_count_pure_ok_is_even$pure(start, end)}
    start < end ==>
        $RangeCountQuantifierHelper_$42_quantifiers_range_count_pure_ok_is_even$pure(start, end) ==
            $RangeCountQuantifierHelper_$42_quantifiers_range_count_pure_ok_is_even$pure(start, end - 1)
            + (if $42_quantifiers_range_count_pure_ok_is_even$pure(end - 1) then 1 else 0)
);
