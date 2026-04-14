module 0x42::foo;

use sui::dynamic_field;
use prover::prover::requires;

public struct SS has copy, drop, store { x: vector<bool> }

public fun look(s: &SS): bool {
    let x = &s.x;
    if (x.is_empty()) { false } else { x[0] }
}

public struct TT has key {id: UID, v: u8}

public fun get_s(t: &TT): &SS {
    dynamic_field::borrow(&t.id, t.v)
}

public fun blah(self: &TT): bool {
    self.get_s().look()
}

#[spec(prove)]
public fun blah_spec(self: &TT): bool {
    requires (dynamic_field::exists_with_type<u8,SS>(&self.id, self.v));
    blah(self)
}
