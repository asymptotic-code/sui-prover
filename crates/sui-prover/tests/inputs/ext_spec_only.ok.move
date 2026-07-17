// Demonstrates that the upstream-compiler-compatible `#[ext(spec_only)]`
// wrapper is accepted equivalently to the bare `#[spec_only]` attribute.
//
// Background: the official Mysten Labs sui CLI's move-compiler does not
// register `spec_only` as a known attribute and emits warning[W02018]
// ("Unknown attribute 'spec_only'. Custom attributes must be wrapped in
// 'ext', e.g. '#[ext(spec_only)]'"). The prover's verification-attribute
// matcher already accepts the bare form (asymptotic-code/sui fork registers
// `VerificationAttribute::SpecOnly`); this test exercises the parallel
// `#[ext(spec_only)]` path through `package_targets::has_bare_ext_attribute`
// + `default_spec_only`.
//
// Parameterized forms (`#[ext(spec_only(loop_inv(...), axiom))]`) are
// intentionally NOT yet supported — those keep the bare syntax for now.

#[allow(unused_function)]
module 0x42::ext_spec_only_test;

#[ext(spec_only)]
use prover::prover::{requires, ensures};

fun double(x: u8): u16 {
    (x as u16) * 2
}

#[spec(prove)]
fun double_spec(x: u8): u16 {
    requires(x <= 50);
    let r = double(x);
    ensures(r <= 100);
    r
}
