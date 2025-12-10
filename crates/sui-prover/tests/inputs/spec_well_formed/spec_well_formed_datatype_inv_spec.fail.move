module 0x42::bad_inv;

public struct S { x: u8 }

#[spec_only]
use prover::prover::ensures;

#[spec_only]
fun S_inv(self: &S): bool {
    self.get_y() > 0
}

public fun get_y(self: &S): u8 {
    get_x(self)
}

public fun get_x(self: &S): u8 {
    self.x
}

#[spec(prove)]
public fun get_x_spec(self: &S): u8 {
    get_x(self)
}

#[spec(prove)]
#[allow(unused)]
fun test(self: &S) {
    ensures(false);
}
