// Per-spec extra_bpl: single-trigger end-step axiom for the `is_even`-indexed
// find_indices helper in nested_pure.ok.move. See find_indices_big.ok.bpl
// for the rationale; the compound-trigger global axioms don't support
// concrete exact-value unfolding from a fresh helper call, so tests that
// assert equality like `find_indices(v, is_even) == vector[1, 3]` need a
// single-trigger axiom scoped to just the spec.

axiom (forall v: Vec (int), start: int, end: int ::
    {$FindIndicesQuantifierHelper_$42_nested_pure_ok_is_even$pure(v, start, end)}
    start < end ==>
    (var res := $FindIndicesQuantifierHelper_$42_nested_pure_ok_is_even$pure(v, start, end);
    (var prev := $FindIndicesQuantifierHelper_$42_nested_pure_ok_is_even$pure(v, start, end - 1);
        (if $42_nested_pure_ok_is_even$pure(ReadVec(v, end - 1)) then
            LenVec(res) == LenVec(prev) + 1 &&
            (forall j: int :: 0 <= j && j < LenVec(prev) ==> ReadVec(res, j) == ReadVec(prev, j)) &&
            ReadVec(res, LenVec(prev)) == end - 1
         else
            LenVec(res) == LenVec(prev) &&
            (forall j: int :: 0 <= j && j < LenVec(prev) ==> ReadVec(res, j) == ReadVec(prev, j)))
    ))
);
