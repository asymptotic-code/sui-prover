module 0x42::foo;

#[spec_only]
use prover::prover::{ensures};

public enum ColorTypeNested has drop, copy {
    Valuabled { red: u32, green: u32, blue: u32 },
    Mono,
}

public enum ColorTest has drop, copy {
    First { a: ColorTypeNested, b: ColorTypeNested },
    Second(ColorTypeNested),
    None,
}

fun reset_nested_colors(color_ref: &mut ColorTest) {
    match (color_ref) {
        ColorTest::First{mut a, mut b} => {
            match (a) {
                ColorTypeNested::Valuabled { red, green, blue } => {
                    *red = 3;
                    *green = 2;
                    *blue = 4;
                },
                ColorTypeNested::Mono => {
                    *a = ColorTypeNested::Valuabled { red: 3, green: 2, blue: 4 }
                }
            }
        },
        ColorTest::Second(x) => {
            match (x) {
                ColorTypeNested::Valuabled { red, green, blue } => {
                    *red = 10;
                    *green = 10;
                    *blue = 10;
                },
                ColorTypeNested::Mono => {
                    *x = ColorTypeNested::Valuabled { red: 10, green: 10, blue: 10 }
                }
            }
        },
        ColorTest::None => {}
    };
}

#[spec(focus)]
fun reset_nested_colors_spec(color_ref: &mut ColorTest) {
    reset_nested_colors(color_ref);

    match (color_ref) {
        ColorTest::First{a, b} => {
            ensures(a == ColorTypeNested::Valuabled{ red: 3, green: 2, blue: 4 });
        },
        ColorTest::Second(x) => {
            ensures(x == ColorTypeNested::Valuabled{ red: 10, green: 10, blue: 10 });
        },
        ColorTest::None => {}
    };
}
