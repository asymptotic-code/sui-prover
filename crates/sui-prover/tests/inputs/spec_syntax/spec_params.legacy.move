// Every `spec` parameter, in the deprecated #[spec(...)] syntax.
// spec_params.new.move is the same file in the new syntax; outputs must match.
module 0x42::spec_params;

use prover::prover::{ensures, asserts};

public fun add(a: u64, b: u64): u64 { a + b }

public fun double(a: u64): u64 { a * 2 }

public fun halve(a: u64): u64 { a / 2 }

public fun quarter(a: u64): u64 { halve(halve(a)) }

public fun pick_smaller(a: u64, b: u64): u64 { if (a < b) a else b }

public fun unfinished(a: u64): u64 { a - 1 }

#[ext(pure, uninterpreted)]
public fun square(x: u64): u128 { (x as u128) * (x as u128) }

public fun use_square(x: u64): u128 { square(x) }

// A bare `spec`: trusted, not verified, used for `halve` in callers' proofs.
#[spec]
fun halve_spec(a: u64): u64 {
    let r = halve(a);
    ensures(r <= a);
    r
}

// The target is inferred from the `_spec` suffix.
#[spec(prove, timeout = 60)]
fun add_spec(a: u64, b: u64): u64 {
    asserts((a as u128) + (b as u128) <= 18446744073709551615);
    let r = add(a, b);
    ensures(r == a + b);
    r
}

#[spec(prove, target = double, ignore_abort)]
fun double_ignoring_aborts(a: u64): u64 {
    let r = double(a);
    ensures(r / 2 == a);
    r
}

#[spec(prove, target = quarter, no_opaque, run_on = b"local")]
fun quarter_spec(a: u64): u64 {
    let r = quarter(a);
    ensures(r <= a);
    r
}

#[spec(prove, boogie_opt = b"{:isolate_paths}")]
fun pick_smaller_spec(a: u64, b: u64): u64 {
    let r = pick_smaller(a, b);
    ensures(r <= a && r <= b);
    r
}

#[spec(prove, interpreted = square)]
fun use_square_spec(x: u64): u128 {
    let r = use_square(x);
    ensures(r == (x as u128) * (x as u128));
    r
}

// Skipped with a reason, so the failing `ensures` is never checked.
#[spec(prove, skip = b"not ready")]
fun unfinished_spec(a: u64): u64 {
    let r = unfinished(a);
    ensures(r == a);
    r
}
