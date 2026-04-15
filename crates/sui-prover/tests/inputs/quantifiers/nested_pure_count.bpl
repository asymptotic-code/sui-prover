// Single-trigger end-step axiom for count with is_even in nested_pure.ok.move.
axiom (forall v: Vec (int), start: int, end: int ::
    {$CountQuantifierHelper_$42_nested_pure_ok_is_even$pure(v, start, end)}
    start < end ==>
        $CountQuantifierHelper_$42_nested_pure_ok_is_even$pure(v, start, end) ==
            $CountQuantifierHelper_$42_nested_pure_ok_is_even$pure(v, start, end - 1)
            + (if $42_nested_pure_ok_is_even$pure(ReadVec(v, end - 1)) then 1 else 0)
);
