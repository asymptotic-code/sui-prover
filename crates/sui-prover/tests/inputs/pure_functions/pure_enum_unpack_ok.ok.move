module 0x42::pure_enum_unpack;

#[spec_only]
use prover::prover::{ensures, requires};

public enum Pair has copy, drop {
    Empty,
    One(u8),
    Two(u8, u8),
}

// Uses unpacked fields non-trivially (arithmetic on both).
#[ext(pure)]
public fun sum(p: Pair): u16 {
    match (p) {
        Pair::Empty => 0,
        Pair::One(a) => (a as u16),
        Pair::Two(a, b) => (a as u16) + (b as u16),
    }
}

#[spec(prove)]
fun test_empty() {
    ensures(sum(Pair::Empty) == 0)
}

#[spec(prove)]
fun test_one() {
    ensures(sum(Pair::One(7)) == 7)
}

#[spec(prove)]
fun test_two() {
    ensures(sum(Pair::Two(3, 4)) == 7)
}

// Relational: sum(Two(a, b)) == sum(One(a)) + sum(One(b)) for all a, b.
#[spec(prove)]
fun test_two_decomp(a: u8, b: u8) {
    requires(sum(Pair::One(a)) + sum(Pair::One(b)) == (a as u16) + (b as u16));
    ensures(sum(Pair::Two(a, b)) == sum(Pair::One(a)) + sum(Pair::One(b)))
}
