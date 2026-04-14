module 0x42::foo;

use prover::prover::{requires, ensures};
use sui::dynamic_field as df;

public struct MyObject has key {
    id: UID,
}

public fun set_scores(uid: &mut UID, key: u64, scores: vector<u64>) {
    df::add(uid, key, scores);
}

#[spec(prove)]
fun verify_set_scores(obj: &mut MyObject, key: u64, scores: vector<u64>) {
    requires(!df::exists_with_type<u64, vector<u64>>(&obj.id, key));
    set_scores(&mut obj.id, key, scores);
    ensures(df::exists_with_type<u64, vector<u64>>(&obj.id, key));
    ensures(*df::borrow<u64, vector<u64>>(&obj.id, key) == scores);
}
