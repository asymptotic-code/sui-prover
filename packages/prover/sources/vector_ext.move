module prover::vector_ext;

/// Spec-only total borrow: returns the element at index `i` if in range,
/// otherwise an unspecified (uninterpreted but deterministic) value.
/// Unlike `vector::borrow`, this never aborts — useful in spec expressions
/// that would otherwise require a bounds guard.
///
/// To use method syntax (`v.borrow_or_unknown(i)`), add at the top of your
/// module: `use fun prover::vector_ext::borrow_or_unknown as vector.borrow_or_unknown;`
#[spec_only]
public native fun borrow_or_unknown<T>(v: &vector<T>, i: u64): &T;

/// Spec-only concatenation: returns `v1 ++ v2`. A non-aborting total
/// function useful in suffix/prefix-invariant proofs.
#[spec_only]
public native fun concat<T>(v1: &vector<T>, v2: &vector<T>): &vector<T>;
