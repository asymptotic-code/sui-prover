// Single-trigger end-step axioms for range_sum_map's per-function helpers.

axiom (forall start: int, end: int ::
    {$RangeSumMapQuantifierHelper_$42_quantifiers_range_sum_map_ok_identity$pure(start, end)}
    start < end ==>
        $RangeSumMapQuantifierHelper_$42_quantifiers_range_sum_map_ok_identity$pure(start, end) ==
            $RangeSumMapQuantifierHelper_$42_quantifiers_range_sum_map_ok_identity$pure(start, end - 1)
            + $42_quantifiers_range_sum_map_ok_identity$pure(end - 1)
);

axiom (forall start: int, end: int ::
    {$RangeSumMapQuantifierHelper_$42_quantifiers_range_sum_map_ok_double$pure(start, end)}
    start < end ==>
        $RangeSumMapQuantifierHelper_$42_quantifiers_range_sum_map_ok_double$pure(start, end) ==
            $RangeSumMapQuantifierHelper_$42_quantifiers_range_sum_map_ok_double$pure(start, end - 1)
            + $42_quantifiers_range_sum_map_ok_double$pure(end - 1)
);
