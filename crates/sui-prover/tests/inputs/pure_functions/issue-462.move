// Tests for issue #462: Equality operations with vectors in pure functions
// Pure functions should use $IsEqual functions instead of direct == and != operators
// to properly handle non-extensional types like vectors

module 0x42::issue_462 {
    use std::vector;

    // Test vector equality in pure function
    #[ext(pure)]
    public fun vec_eq(v1: &vector<u64>, v2: &vector<u64>): bool {
        v1 == v2
    }

    // Test vector inequality in pure function
    #[ext(pure)]
    public fun vec_neq(v1: &vector<u64>, v2: &vector<u64>): bool {
        v1 != v2
    }

    // Test vector equality with conditionals
    #[ext(pure)]
    public fun vec_eq_conditional(v1: &vector<u64>, v2: &vector<u64>): u64 {
        if (v1 == v2) {
            1
        } else {
            0
        }
    }

    // Test vector inequality with conditionals
    #[ext(pure)]
    public fun vec_neq_conditional(v1: &vector<u64>, v2: &vector<u64>): u64 {
        if (v1 != v2) {
            1
        } else {
            0
        }
    }

    // Spec function that uses vector equality checks
    #[spec(focus)]
    public fun test_vec_eq_spec() {
        let v1 = vector::empty<u64>();
        let v2 = vector::empty<u64>();
        spec {
            assert vec_eq(&v1, &v2) == true;
        };
    }

    // Spec function that uses vector inequality checks
    #[spec(focus)]
    public fun test_vec_neq_spec() {
        let mut v1 = vector::empty<u64>();
        let v2 = vector::empty<u64>();
        vector::push_back(&mut v1, 1);
        spec {
            assert vec_neq(&v1, &v2) == true;
        };
    }
}
