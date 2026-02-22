module 0x42::foo;

public fun f(x: u8): u8 {
    x
}

#[spec(prove)]
public fun f_spec(x: u8): u8 {
    f(x)
}
