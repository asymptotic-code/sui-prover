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
            *blue = 2;
        },
        Color::Hex(x) => {
            *x = 0;
        },
        Color::Mono => {
            *color_ref = Color::RGB { red: 0, green: 0, blue: 0 }
        }
    };
}

#[spec(prove)]
fun reset_color_spec(color_ref: &mut Color) {
    let before = *color_ref;
    reset_color(color_ref);

    match (before) {
        Color::RGB{red, green, blue} => {
            ensures(color_ref == Color::RGB{ red: 2, green, blue: 2 });
        },
        Color::Hex(x) => {
            ensures(color_ref == Color::Hex(0));
        },
        Color::Mono => {
            ensures(color_ref == Color::RGB{ red: 0, green: 0, blue: 0 });
        }
    };
}
