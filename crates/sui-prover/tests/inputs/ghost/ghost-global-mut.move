module 0x42::foo;

use prover::ghost;
use prover::prover::{asserts, requires};

public struct Counter {}

public fun foo(x: &mut u64): u64 {
    bar(x)
}

public fun bar(x: &mut u64): u64 { *x = *x + 1; *x }

#[spec(prove)]
public fun foo_spec(x: &mut u64): u64 {
    ghost::declare_global_mut<Counter, u64>();
    requires(ghost::global<Counter, u64>() == x);

    asserts(*ghost::global<Counter, u64>() < std::u64::max_value!());
    let res = foo(x);

    res
}

#[spec(prove, no_opaque)]
public fun bar_spec(x: &mut u64): u64 {
    ghost::declare_global_mut<Counter, u64>();

    asserts(*x < std::u64::max_value!());
    let res = bar(x);
    ghost::set<Counter, u64>(&res);

    res
}
