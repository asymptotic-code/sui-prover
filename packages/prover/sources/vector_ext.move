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

/// Spec-only functional append: returns `v1 ++ v2`. Pure counterpart to
/// `std::vector::append(v1: &mut, v2)`. Never aborts.
#[spec_only]
public native fun append_pure<T>(v1: &vector<T>, v2: &vector<T>): &vector<T>;

/// Spec-only functional push_back: returns `v` with `e` appended.
#[spec_only]
public native fun push_back_pure<T>(v: &vector<T>, e: &T): &vector<T>;

/// Spec-only functional pop_back: returns `v` with its last element dropped.
/// If `v` is empty, returns `v` unchanged.
#[spec_only]
public native fun pop_back_pure<T>(v: &vector<T>): &vector<T>;

/// Spec-only functional push_front: returns `v` with `e` prepended.
/// No std::vector counterpart — a pure extension.
#[spec_only]
public native fun push_front_pure<T>(v: &vector<T>, e: &T): &vector<T>;

/// Spec-only functional pop_front: returns `v` with its first element dropped.
/// If `v` is empty, returns `v` unchanged. No std::vector counterpart.
#[spec_only]
public native fun pop_front_pure<T>(v: &vector<T>): &vector<T>;

/// Spec-only functional insert: returns `v` with `e` inserted at index `i`.
/// If `i > length(v)`, returns `v` unchanged.
#[spec_only]
public native fun insert_pure<T>(v: &vector<T>, e: &T, i: u64): &vector<T>;

/// Spec-only functional remove: returns `v` with the element at `i` dropped.
/// If `i >= length(v)`, returns `v` unchanged.
#[spec_only]
public native fun remove_pure<T>(v: &vector<T>, i: u64): &vector<T>;
