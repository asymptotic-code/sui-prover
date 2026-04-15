module prover::vec_map_ext;

use sui::vec_map::VecMap;

/// Spec-only total lookup: returns the value at `key` if contained, else an
/// uninterpreted but deterministic value. Unlike `vec_map::get`, this never
/// aborts — useful in spec expressions that would otherwise need a guard.
///
/// Method syntax: `use fun prover::vec_map_ext::get_or_unknown as VecMap.get_or_unknown;`
#[spec_only]
public native fun get_or_unknown<K: copy, V>(m: &VecMap<K, V>, k: &K): &V;

/// Spec-only total indexed entry access: returns `(&K, &V)` at insertion-order
/// index `i` if in range, else an uninterpreted but deterministic pair.
/// Unlike `vec_map::get_entry_by_idx`, this never aborts.
///
/// Method syntax: `use fun prover::vec_map_ext::get_entry_by_idx_or_unknown as VecMap.get_entry_by_idx_or_unknown;`
#[spec_only]
public native fun get_entry_by_idx_or_unknown<K: copy, V>(m: &VecMap<K, V>, i: u64): (&K, &V);

/// Spec-only total index lookup: returns the insertion-order index of `key`
/// if contained, else an uninterpreted but deterministic value.
/// Unlike `vec_map::get_idx`, this never aborts.
#[spec_only]
public native fun get_idx_or_unknown<K: copy, V>(m: &VecMap<K, V>, k: &K): u64;

/// Spec-only functional insert: returns the map obtained by appending
/// `(k, v)` as a new entry. Callers should guarantee `!m.contains(&k)` for
/// the result to satisfy VecMap's no-duplicate-keys invariant.
#[spec_only]
public native fun insert_pure<K: copy, V>(m: &VecMap<K, V>, k: &K, v: &V): &VecMap<K, V>;

/// Spec-only functional remove: returns the map with `k`'s entry removed if
/// present, else the same map unchanged. Never aborts.
#[spec_only]
public native fun remove_pure<K: copy, V>(m: &VecMap<K, V>, k: &K): &VecMap<K, V>;
