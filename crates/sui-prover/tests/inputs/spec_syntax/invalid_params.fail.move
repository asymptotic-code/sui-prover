module 0x42::invalid_params;

public struct S has drop { x: u64 }

public fun foo(): u64 {
    1
}

// Each item below breaks one rule of the deprecated #[spec(...)] /
// #[spec_only(...)] parsers, which ext(spec(...)) / ext(spec_only(...)) follow.

#[mode(spec), ext(spec(prove, target = foo, unknown_param))]
fun unknown_spec_param(): u64 { foo() }

#[mode(spec), ext(spec(prove, target = foo, focus, skip))]
fun focus_and_skip(): u64 { foo() }

#[mode(spec), ext(spec(prove, target = foo, timeout = 0))]
fun zero_timeout(): u64 { foo() }

#[mode(spec), ext(spec(prove, target = b"foo"))]
fun target_not_a_path(): u64 { foo() }

#[mode(spec), ext(spec(prove, target = foo, boogie_opt = 1))]
fun boogie_opt_not_a_bytestring(): u64 { foo() }

#[mode(spec), ext(spec(prove, target = foo, extra_bpl(a = b"x.bpl", b = b"x.bpl")))]
fun duplicate_extra_bpl(): u64 { foo() }

#[mode(spec), ext(spec = b"prove")]
fun assigned_spec(): u64 { foo() }

#[mode(spec), ext(spec_only(unknown_param))]
fun unknown_spec_only_param(): bool { true }

#[mode(spec), ext(spec_only(axiom, extra_bpl = b"x.bpl"))]
fun axiom_not_standalone(): bool { true }

#[mode(spec), ext(spec_only(loop_inv(target = foo), extra_bpl = b"x.bpl"))]
fun loop_inv_not_standalone(): bool { true }

#[mode(spec), ext(spec_only(loop_inv(label = 0)))]
fun loop_inv_without_target(): bool { true }

#[mode(spec), ext(spec_only(loop_inv(target = foo, label = b"0")))]
fun loop_inv_label_not_a_number(): bool { true }

#[mode(spec), ext(spec_only(inv_target = 0x42::invalid_params::S, include = 0x42::invalid_params::foo))]
fun inv_target_and_include(s: &S): bool { s.x > 0 }
