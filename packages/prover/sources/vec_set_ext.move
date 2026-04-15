module prover::vec_set_ext;

use sui::vec_set::VecSet;

/// Spec-only functional insert: returns the set obtained by appending `k`
/// as a new key. Callers should guarantee `!s.contains(&k)` for the result
/// to satisfy VecSet's no-duplicate-keys invariant.
#[spec_only]
public native fun insert_pure<K: copy + drop>(s: &VecSet<K>, k: &K): &VecSet<K>;

/// Spec-only functional remove: returns the set with `k` removed if present,
/// else the same set unchanged. Never aborts.
#[spec_only]
public native fun remove_pure<K: copy + drop>(s: &VecSet<K>, k: &K): &VecSet<K>;
