module 0x42::global_set_issue;

public struct Foo has copy, drop {}

use prover::ghost::{declare_global_mut, borrow_mut, set};
use prover::prover::ensures;

fun set_twice() {
}

#[spec(prove)]
fun set_twice_spec() {
    declare_global_mut<Foo, u8>();
    set<Foo, u8>(&1);
    set_twice();
    set<Foo, u8>(&2);
}

#[spec(prove)]
fun miracle() {
    declare_global_mut<Foo, u8>(); 
    set_twice();
    let x = borrow_mut<Foo, u8>();
    ensures(*x == 2);
}