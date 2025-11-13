module 0x42::A {
    use std::option::some;
    fun foo(x: Option<u8>): Option<u8> {
        if (x.is_some()) {
            x
        } else {
            some(0)
        }
    }

    #[spec(prove)]
    fun foo_spec(x: Option<u8>): Option<u8> {
        foo(x)
    }
}

module 0x42::B {
    use std::option::some;
    use prover::prover::{val, drop};

    #[spec_only(inv_target=std::option::Option)]
    fun Option_inv<T>(self: &Option<T>): bool {
        if (self.is_some()) {
            let o = val(self.borrow());
            let x = some(o);
            let b = self == x;
            drop(x);
            b
        } else {
            true
        }
    }
}
