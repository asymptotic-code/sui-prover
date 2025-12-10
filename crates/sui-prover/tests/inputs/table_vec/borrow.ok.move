module 0x42::foo;

use sui::table_vec::TableVec;

fun foo(t: &TableVec<u8>, i: u64): u8 {
    if (i < t.length()) {
        t[i]
    } else {
        0
    }
}

#[spec(prove)]
fun foo_spec(t: &TableVec<u8>, i: u64): u8 {
    foo(t, i)
}
