module 0x42::foo;

#[spec_only]
use prover::prover::requires;
#[spec_only]
use prover::vector_iter::filter;

public struct Foo {
    x: u64,
}

#[spec_only, ext(pure)]
fun foo_property(
    v1: &vector<Foo>,
    v2: &vector<Foo>,
    x: u64,
): bool {
    v1 == filter!(v2, |foo| is_x(foo, x))
}

#[spec_only, ext(pure)]
fun is_x(foo: &Foo, x: u64): bool {
    foo.x == x
}

#[spec(prove)]
fun foo_spec(v1: &vector<Foo>, v2: &vector<Foo>, x: u64) {
    requires(foo_property(v1, v2, x));
}
