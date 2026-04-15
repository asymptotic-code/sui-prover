module prover::dynamic_field_ext;

use sui::object::UID;

/// Spec-only total borrow: returns the value stored under `name` on `object`
/// if present, else an uninterpreted but deterministic value. Unlike
/// `dynamic_field::borrow`, this never aborts — useful in spec expressions
/// that would otherwise need a guard.
#[spec_only]
public native fun borrow_or_unknown<Name: copy + drop + store, Value: store>(object: &UID, name: Name): &Value;
