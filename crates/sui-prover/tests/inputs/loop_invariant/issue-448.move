module 0x42::issue_448;

public fun few(x: u8, z: u8) {
    let mut y = 0;
    while (y < x) {
        y = y + 1;
    };
    let mut i = z;
    while (i > y) {
        i = i - 1;
    }
}

#[mode(spec), ext(spec(loop_inv(target = few, label = 0)), pure)]
#[allow(unused_function)]
fun inv1(y: u8, x: u8): bool {
    y <= x
}

#[mode(spec), ext(spec(loop_inv(target = few, label = 1)), pure)]
#[allow(unused_function)]
fun inv2(i: u8, z: u8): bool {
    i <= z
}

#[spec(prove)]
public fun few_spec(x: u8, z: u8) {
    few(x, z)
}
