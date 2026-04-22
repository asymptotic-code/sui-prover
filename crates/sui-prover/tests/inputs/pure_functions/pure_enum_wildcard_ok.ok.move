module 0x42::pure_enum_wildcard;

#[spec_only]
use prover::prover::ensures;

public enum Color has copy, drop {
    Red,
    Green,
    Blue,
    Custom(u8, u8, u8),
}

// Wildcard `_` catch-all arm.
#[ext(pure)]
public fun is_primary(c: Color): bool {
    match (c) {
        Color::Red => true,
        Color::Green => true,
        Color::Blue => true,
        _ => false,
    }
}

// Wildcard within a variant pattern plus a wildcard catch-all.
#[ext(pure)]
public fun red_channel(c: Color): u8 {
    match (c) {
        Color::Red => 255,
        Color::Custom(r, _, _) => r,
        _ => 0,
    }
}

#[spec(prove)]
fun test_primary_red() {
    ensures(is_primary(Color::Red))
}

#[spec(prove)]
fun test_primary_custom() {
    ensures(!is_primary(Color::Custom(1, 2, 3)))
}

#[spec(prove)]
fun test_red_channel_custom(g: u8, b: u8) {
    ensures(red_channel(Color::Custom(42, g, b)) == 42)
}

#[spec(prove)]
fun test_red_channel_green() {
    ensures(red_channel(Color::Green) == 0)
}
