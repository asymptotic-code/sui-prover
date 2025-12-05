module 0x42::loop_invariant_external_aborts_fail;

#[spec_only(loop_inv(target=bar)), ext(no_abort)]
fun bar_loop_inv(i: u64, stop: u64, v__3: &vector<u8>): bool {
    i <= stop && v__3.length() == stop - i
}

// Available variables: ( v: vector<u8>, v__1: vector<u8>, $stop: u64, i: u64, r: vector<u8>, stop: u64, v__3: vector<u8> )

// fun bar_expanded(v: vector<u8>): vector<u8> {
//     // v.map!(|x| 0)  // so f = |x| x
//     // =>
//     let v_2 = v;
//     let mut r = vector[];
//     // v_2.do!(|e| r.push_back($f(e))) // so f' = |e| r.push_back(0)
//     // =>
//     let mut v_3 = v_2;
//     v_3.reverse();
//     // v_3.length().do!(|_| $f'(v_3.pop_back())) // so f'' = |_| r.push_back(v_3.pop_back())
//     // =>
//     // std::macros::do!(v_3.length(), f'')
//     // => std::macros::range_do!(0, v_3.length(), |i| r.push_back(0))
//     // =>
//     let mut i = 0;
//     let stop = v_3.length();
//     while (i < stop) {
//         r.push_back(v_3.pop_back()); // $f''(i)
//         i = i+1;
//     };
//     // end std::macros::range_do!, u64::do!,
//     v_3.destroy_empty();
//     // end v_2.do!
//     r
// }

public fun bar(v: vector<u8>): vector<u8> {
    v.map!(|_x| 0)
}

#[spec(prove)]
fun bar_spec(v: vector<u8>): vector<u8> {
    bar(v)
}