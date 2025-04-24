module 0x42::inv_foo {
    public struct Bar {
        x: u64
    }

    public fun set_value(bar: &mut Bar, value: u64) {
        bar.x = value; 
    }

    public fun get_values(bar: &Bar): u64 {
        bar.x
    }

    public fun increment(bar: &mut Bar) {
        bar.set_value(150);
    }

    #[spec_only]
    public fun foo_inv(bar: &Bar): bool {
        bar.x < 150
    }

    #[spec(prove)]
    public fun increment_spec(bar: &mut Bar) {
        bar.increment();
    }
}