module 0x42::foo;

#[spec_only]
use prover::prover::{ensures};

public enum Color has drop, copy {
    RGB { red: u32, green: u32, blue: u32 },
    Hex(u32),
    Mono,
}

fun reset_color(color_ref: &mut Color) {
    match (color_ref) {
        Color::RGB{mut red, mut green, mut blue} => {
            *red = 2;
            *green = 3;
            *blue = 2;
        },
        Color::Hex(x) => {
            *color_ref = Color::RGB { red: 0, green: 0, blue: 0 }
        },
        Color::Mono => {
            *color_ref = Color::RGB { red: 1, green: 2, blue: 3 }
        }
    };
}

#[spec(prove)]
fun reset_color_spec(color_ref: &mut Color) {
    let before = *color_ref;
    reset_color(color_ref);

    match (before) {
        Color::RGB{red, green, blue} => {
            ensures(color_ref == Color::RGB{ red: 2, green: 3, blue: 2 });
        },
        Color::Hex(x) => {
            ensures(color_ref == Color::RGB{ red: 0, green: 0, blue: 0 });
        },
        Color::Mono => {
            ensures(color_ref == Color::RGB{ red: 1, green: 2, blue: 3 });
        }
    };
}

// new test
// 1) raw data in a struct
public struct ColorData has drop, copy {
    red: u32,
    green: u32,
    blue: u32,
}

// 2) enum now *wraps* that struct
public enum ColorEnum has drop, copy {
    Valuabled(ColorData),
    Mono,
}

// 3) reset_to_low on the enum
fun reset(col: &mut ColorEnum) {
    match (col) {
        ColorEnum::Valuabled(data) => {
            // mutate in place
            data.red = 3;
            data.green = 2;
            data.blue = 4;
        },
        ColorEnum::Mono => {}
    }
}

#[spec(focus)]
fun reset_spec(col: &mut ColorEnum) {
    reset(col);
    match (col) {
        ColorEnum::Valuabled(d) => {
            ensures(d == ColorData {
                red:   3,
                green: 2,
                blue:  4,
            });
        },
        ColorEnum::Mono => {}
    };
}
