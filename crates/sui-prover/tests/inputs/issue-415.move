module 0x42::foo;

#[ext(pure)]
fun test1(j: u64, v: &vector<u8>, w: &vector<u8>): bool {
    if (j < v.length() && j < w.length()) {
        v[v.length() - (j+1)] == w[j] 
    } else {
        true
    }
}

#[spec(prove)]
public fun test_spec(j: u64, v: &vector<u8>, w: &vector<u8>): bool {
    let res = test1(j, v, w);
    res
}