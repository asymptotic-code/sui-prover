module 0x42::a {
    public struct Sa<phantom T: store> has key, store { id: UID }
    public struct Key() has copy, drop, store;
    public fun is_in_good_state<T: store>(self: &Sa<T>): bool {
        sui::dynamic_field::exists_with_type<Key, T>(&self.id, Key())
    }
}

#[allow(unused_use)]
module 0x42::b {
    use 0x42::a::{Sa, is_in_good_state};
    public struct Sb {
        x: Sa<u8>
    }
    public fun x(self: &Sb): &Sa<u8> {
        &self.x
    }
}

module 0x42::c {
    use 0x42::b::{Sb};

    #[spec_only(inv_target=Sb)]
    public fun Sb_inv(self: &Sb): bool {
        self.x().is_in_good_state()
    }
}

#[allow(unused_variable)]
module 0x42::d {
    use 0x42::b::{Sb};

    public fun f(x: &Sb) {
        // empty
    }

    #[spec(prove)]
    fun f_spec(x: &Sb) {
        prover::prover::requires(0x42::c::Sb_inv(x));
        f(x)
    }
}
