module 0x42::foo;

#[spec_only]
use prover::prover::{ensures};

public enum ColorType has drop, copy {
    Valuabled { red: u32, green: u32, blue: u32 },
    Mono,
}

public struct ColorStruct has drop, copy {
    inner: ColorType,
    val: u32,
}

fun reset_to_low(data: &mut ColorStruct) {
    data.val = 1;
    match (&mut data.inner) {
        ColorType::Valuabled { red, green, blue } => {
            *red = 3;
            *green = 2;
            *blue = 4;
        },
        ColorType::Mono => {
            data.inner = ColorType::Valuabled { red: 3, green: 2, blue: 4 };
        }
    }
}

#[spec(focus)]
fun reset_to_low_spec(cn: &mut ColorStruct) {
    reset_to_low(cn);
    ensures(
        cn.inner ==
        ColorType::Valuabled { red: 3, green: 2, blue: 4 }
    );
    ensures(cn.val == 1);
}
