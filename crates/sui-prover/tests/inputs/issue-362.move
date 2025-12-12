module 0x42::A {
    use 0x42::foo::find_odd_index2;
    use prover::vector_iter::{any_range, find_index};
    use prover::prover::ensures;

    #[ext(pure)]
    public fun is_odd(x: &u64): bool {
        (*x)%2 == 1
    }

    #[spec_only(loop_inv(target=0x42::foo::find_odd_index2)), ext(pure)]
    fun foo_inv(v: &vector<u64>, i: u64): bool {
        i <= v.length() && !any_range!(v, 0, i, |x| is_odd(x))
    }

    #[spec(prove, target=0x42::foo::find_odd_index2)]
    fun find_odd_index2_spec(w: &vector<u64>): Option<u64> {
        let r = find_odd_index2(w);
        ensures(r == find_index!(w, |j| is_odd(j)));
        r
    }
}

module 0x42::foo {
    // duplicate of A::is_odd to prevent dependency cycle
    #[ext(pure)]
    public fun is_odd(x: &u64): bool {
        (*x)%2 == 1
    }

    public fun find_odd_index2(w: &vector<u64>): Option<u64> {
        w.find_index!(|x| is_odd(x))
    }
}
