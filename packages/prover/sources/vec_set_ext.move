module prover::vec_set_ext;

use sui::vec_set::VecSet;

/// Spec-only total indexed access: returns the `i`-th key (in insertion
/// order) if `i` is in range, else an uninterpreted but deterministic value.
/// Never aborts — useful for spec expressions that reason about set contents
/// without an explicit bounds guard.
///
/// Method syntax: `use fun prover::vec_set_ext::at_or_unknown as VecSet.at_or_unknown;`
#[spec_only]
public native fun at_or_unknown<K: copy + drop>(s: &VecSet<K>, i: u64): &K;
