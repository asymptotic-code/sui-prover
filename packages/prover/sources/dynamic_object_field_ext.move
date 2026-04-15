module prover::dynamic_object_field_ext;

use sui::object::UID;

/// Spec-only total borrow: returns the object stored under `name` on `object`
/// if present, else an uninterpreted but deterministic value. Unlike
/// `dynamic_object_field::borrow`, this never aborts — useful in spec
/// expressions that would otherwise need a guard.
#[spec_only]
public native fun borrow_or_unknown<Name: copy + drop + store, Value: key + store>(object: &UID, name: Name): &Value;
