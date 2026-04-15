module prover::object_table_ext;

use sui::object_table::ObjectTable;

/// Spec-only total borrow: returns the value at `key` if contained, else an
/// uninterpreted but deterministic value. Unlike `object_table::borrow`, this
/// never aborts — useful in spec expressions that would otherwise need a guard.
///
/// Method syntax: `use fun prover::object_table_ext::borrow_or_unknown as ObjectTable.borrow_or_unknown;`
#[spec_only]
public native fun borrow_or_unknown<K: copy + drop + store, V: key + store>(t: &ObjectTable<K, V>, k: K): &V;
