module 0x42::foo;

#[spec_only]
use prover::prover::ensures;
use prover::log;
use prover::ghost;

public fun foo(x: bool) {
    ghost::set<u64, bool>(&x);
}

#[spec(prove)]
public fun foo_spec(x: bool) {
    ghost::declare_global_mut<u64, bool>();
    foo(x);
    log::ghost<u64, bool>();
    ensures(ghost::global<u64, bool>() != true);
}
