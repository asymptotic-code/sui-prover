// Single-trigger end-step axiom for range_sum_map's identity helper
// in range_sum_map_pure.ok.move.

axiom (forall start: int, end: int ::
    {$RangeSumMapQuantifierHelper_$42_quantifiers_range_sum_map_pure_ok_identity$pure(start, end)}
    start < end ==>
        $RangeSumMapQuantifierHelper_$42_quantifiers_range_sum_map_pure_ok_identity$pure(start, end) ==
            $RangeSumMapQuantifierHelper_$42_quantifiers_range_sum_map_pure_ok_identity$pure(start, end - 1)
            + $42_quantifiers_range_sum_map_pure_ok_identity$pure(end - 1)
);
