// Single-trigger end-step axioms for count's per-predicate helpers.
// These let the multi-pattern prelude axioms unfold on concrete vectors.

axiom (forall v: Vec (int), start: int, end: int ::
    {$CountQuantifierHelper_$42_quantifiers_count_ok_x_is_10$pure(v, start, end)}
    start < end ==>
        $CountQuantifierHelper_$42_quantifiers_count_ok_x_is_10$pure(v, start, end) ==
            $CountQuantifierHelper_$42_quantifiers_count_ok_x_is_10$pure(v, start, end - 1)
            + (if $42_quantifiers_count_ok_x_is_10$pure(ReadVec(v, end - 1)) then 1 else 0)
);

axiom (forall v: Vec (int), start: int, end: int ::
    {$CountQuantifierHelper_$42_quantifiers_count_ok_x_is_positive$pure(v, start, end)}
    start < end ==>
        $CountQuantifierHelper_$42_quantifiers_count_ok_x_is_positive$pure(v, start, end) ==
            $CountQuantifierHelper_$42_quantifiers_count_ok_x_is_positive$pure(v, start, end - 1)
            + (if $42_quantifiers_count_ok_x_is_positive$pure(ReadVec(v, end - 1)) then 1 else 0)
);

axiom (forall v: Vec (int), start: int, end: int ::
    {$CountQuantifierHelper_$42_quantifiers_count_ok_x_is_greater_than_100$pure(v, start, end)}
    start < end ==>
        $CountQuantifierHelper_$42_quantifiers_count_ok_x_is_greater_than_100$pure(v, start, end) ==
            $CountQuantifierHelper_$42_quantifiers_count_ok_x_is_greater_than_100$pure(v, start, end - 1)
            + (if $42_quantifiers_count_ok_x_is_greater_than_100$pure(ReadVec(v, end - 1)) then 1 else 0)
);
