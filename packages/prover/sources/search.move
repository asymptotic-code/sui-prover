/// Generic binary search algorithms for formal verification.
/// These natives provide provably terminating search implementations.
///
/// Note: Since Move natives cannot accept function parameters, each module
/// must define its own search function. This module provides the Lean implementation
/// that can be imported and adapted.
module prover::search {
    // This module is currently empty in Move - the binary search natives
    // are defined directly in the modules that need them (like tick_math_specs).
    //
    // The Lean side provides generic SearchOps.binary_search that can be
    // instantiated for specific use cases.
}
