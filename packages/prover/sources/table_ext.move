module prover::table_ext;

use sui::table::Table;

/// Spec-only total borrow: returns the value at `key` if contained, else an
/// uninterpreted but deterministic value. Unlike `table::borrow`, this never
/// aborts — useful in spec expressions that would otherwise need a guard.
///
/// Method syntax: `use fun prover::table_ext::borrow_or_unknown as Table.borrow_or_unknown;`
#[spec_only]
public native fun borrow_or_unknown<K: copy + drop + store, V: store>(t: &Table<K, V>, k: K): &V;
