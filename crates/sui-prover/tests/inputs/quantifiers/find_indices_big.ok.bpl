// Per-spec extra_bpl: single-trigger end-step axiom for the `is_even`-indexed
// find_indices helper. The global find_indices axiom set uses compound
// triggers on both end-step and start-step so that suffix-invariant loop
// proofs work (see find_indices_suffix_loop.ok.move) without matching loops
// on a single fresh helper call. The downside is that concrete exact-value
// verification of `find_indices(v, p) == vector[...]` can't unfold the helper
// from a fresh call.
//
// This per-spec extra_bpl adds back a single-trigger end-step axiom — but
// only for this specific helper instance on this specific test. It lets Z3
// unfold `find_indices(v, 0, 8)` into `find_indices(v, 0, 7) ++ ...` down
// to the base case, which is enough to pin the result to `vector[1, 3, 5, 7]`.
//
// The axiom is structurally identical to the one the quantifier_helpers_module
// Tera macro would generate if the helper used a single trigger. Unlike the
// `prelude_extra` option, `#[spec(..., extra_bpl = ...)]` is appended only
// to the bpl generated for this spec, so the axiom doesn't leak into
// `funs_abort_check.bpl` or other tests.

axiom (forall v: Vec (int), start: int, end: int ::
    {$FindIndicesQuantifierHelper_$42_quantifiers_find_indices_big_ok_is_even$pure(v, start, end)}
    start < end ==>
    (var res := $FindIndicesQuantifierHelper_$42_quantifiers_find_indices_big_ok_is_even$pure(v, start, end);
    (var prev := $FindIndicesQuantifierHelper_$42_quantifiers_find_indices_big_ok_is_even$pure(v, start, end - 1);
        (if $42_quantifiers_find_indices_big_ok_is_even$pure(ReadVec(v, end - 1)) then
            LenVec(res) == LenVec(prev) + 1 &&
            (forall j: int :: 0 <= j && j < LenVec(prev) ==> ReadVec(res, j) == ReadVec(prev, j)) &&
            ReadVec(res, LenVec(prev)) == end - 1
         else
            LenVec(res) == LenVec(prev) &&
            (forall j: int :: 0 <= j && j < LenVec(prev) ==> ReadVec(res, j) == ReadVec(prev, j)))
    ))
);
