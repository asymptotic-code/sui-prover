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

#[spec_only(loop_inv(target = few, label = 0)), ext(pure)]
fun inv1(y: u8, x: u8): bool {
    y <= x
}

#[spec_only(loop_inv(target = few, label = 1)), ext(pure)]
fun inv2(i: u8, z: u8): bool {
    i <= z
}

#[spec(prove)]
public fun few_spec(x: u8, z: u8) {
    few(x, z)
}
