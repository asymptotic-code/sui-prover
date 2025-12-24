#[allow(unused)]
module 0x42::quantifiers_range_map_ok;

#[spec_only]
use prover::prover::ensures;

#[spec_only]
use prover::vector_iter::range_map;

#[ext(pure)]
fun x_plus_10(x: u64): u64 {
    if (x < std::u64::max_value!() - 10) {
        x + 10
    } else {
        std::u64::max_value!()
    }
}

#[ext(pure)]
fun x_plus_10_plus_n(x: u64, n: u64): u64 {
    if (x < std::u64::max_value!() - 10) {
        if (n < std::u64::max_value!() - x - 10) {
            x + 10 + n
        } else {
            std::u64::max_value!()
        }
    } else {
        std::u64::max_value!()
    }
}


#[spec(prove)]
fun test_spec_r() {
    ensures(range_map!<u64>(1, 2, |x| x_plus_10_plus_n(x, 3)) == vector[14]);
}

#[spec(prove)]
fun test_spec() {
    ensures(range_map!<u64>(0, 0, |x| x_plus_10(x)) == vector[]);
    ensures(range_map!<u64>(4, 7, |x| x_plus_10(x)) == vector[14, 15, 16]);
}

// Pure Test: range_map

#[ext(pure)]
fun double(x: u64): u64 {
    if (x > 9_000_000_000) {
        x
    } else {
        x * 2
    }
}

#[ext(pure)]
fun fn_range_map(start: u64, end: u64): &vector<u64> {
    range_map!<u64>(start, end, |x| double(x))
}

#[spec(prove)]
fun test_range_map() {
    ensures(fn_range_map(0, 2) == vector[0, 2]);
}
