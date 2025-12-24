module 0x42::loop_invariant_external_clone_mut;

use prover::prover::{requires, ensures};

public struct Foo {
    x: u64,
    y: u64,
}

public fun foo(s: &mut Foo) {
    let mut i = 0;
    while (i < s.y) {
        s.x = s.x + 1;
        i = i + 1;
    }
}

#[spec_only(loop_inv(target = foo)), ext(pure)]
public fun foo_inv(s: &Foo, i: u64, __old_s: &Foo): bool {
    i <= s.y &&
    s.x.to_int() == __old_s.x.to_int().add(i.to_int()) &&
    s.y == __old_s.y
}

#[spec(prove)]
public fun foo_spec(s: &mut Foo) {
    let old_x = s.x;
    let old_y = s.y;
    requires((s.x as u128) + (s.y as u128) < std::u64::max_value!() as u128);
    foo(s);
    ensures(s.x == old_x + old_y);
    ensures(s.y == old_y);
}
