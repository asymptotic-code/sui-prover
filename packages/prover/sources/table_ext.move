module prover::table_ext;

use sui::table::Table;

/// Spec-only total borrow: returns the value at `key` if contained, else an
/// uninterpreted but deterministic value. Unlike `table::borrow`, this never
/// aborts — useful in spec expressions that would otherwise need a guard.
///
/// Method syntax: `use fun prover::table_ext::borrow_or_unknown as Table.borrow_or_unknown;`
#[spec_only]
public native fun borrow_or_unknown<K: copy + drop + store, V: store>(t: &Table<K, V>, k: K): &V;

/// Spec-only functional add: returns the table obtained by inserting `(k, v)`.
/// Callers should guarantee `!t.contains(k)` for the result to satisfy the
/// no-duplicate-keys invariant.
#[spec_only]
public native fun add_pure<K: copy + drop + store, V: store>(t: &Table<K, V>, k: K, v: &V): &Table<K, V>;

/// Spec-only functional remove: returns the table with `k`'s entry removed
/// if present, else the same table unchanged. Never aborts.
#[spec_only]
public native fun remove_pure<K: copy + drop + store, V: store>(t: &Table<K, V>, k: K): &Table<K, V>;
