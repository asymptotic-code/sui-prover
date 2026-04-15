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
