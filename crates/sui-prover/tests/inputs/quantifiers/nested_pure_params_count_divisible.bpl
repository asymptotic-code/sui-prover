// Single-trigger end-step axiom for count with is_divisible_by in nested_pure_params.
axiom (forall v: Vec (int), start: int, end: int, $t1: int ::
    {$CountQuantifierHelper_$42_nested_pure_ok_is_divisible_by$pure(v, start, end, $t1)}
    start < end ==>
        $CountQuantifierHelper_$42_nested_pure_ok_is_divisible_by$pure(v, start, end, $t1) ==
            $CountQuantifierHelper_$42_nested_pure_ok_is_divisible_by$pure(v, start, end - 1, $t1)
            + (if $42_nested_pure_ok_is_divisible_by$pure(ReadVec(v, end - 1), $t1) then 1 else 0)
);
