module 0x42::vector_take_fail_test;

// This should fail because we're trying to take more elements than exist
public fun test_take_fail() {
    let v = vector[0, 1, 2];
    vector::take(v, 4); // Trying to take 4 elements from a 3-element vector
}

#[spec(prove, ignore_abort)]
fun test_take_fail_spec() {
    test_take_fail(); // This should abort and that's expected
}
