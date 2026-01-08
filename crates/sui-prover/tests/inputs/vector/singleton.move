module 0x42::vector_singleton;

use prover::prover::ensures;


#[ext(pure)]
public fun make_s<T: copy + drop>(e: T): vector<T> {
    vector::singleton(e)
}

#[spec(prove)]
fun my_spec<T: copy + drop>(e: T): vector<T> {
    let r = make_s<T>(e);
    ensures(vector::length(&r) == 1);
    ensures(*vector::borrow(&r, 0) == e);
    ensures(vector::singleton(e) == r);
    r
}
