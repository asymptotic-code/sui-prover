module prover::vec_map_ext;

use sui::vec_map::VecMap;

/// Spec-only total lookup: returns the value at `key` if contained, else an
/// uninterpreted but deterministic value. Unlike `vec_map::get`, this never
/// aborts — useful in spec expressions that would otherwise need a guard.
///
/// Method syntax: `use fun prover::vec_map_ext::get_or_unknown as VecMap.get_or_unknown;`
#[spec_only]
public native fun get_or_unknown<K: copy, V>(m: &VecMap<K, V>, k: &K): &V;
