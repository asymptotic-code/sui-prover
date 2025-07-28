module 0x42::foo;

use sui::{
    vec_map::VecMap,
};

public struct Stuff has store {
    value: VecMap<u32, bool>,
}

public(package) fun foo(
    self: &mut Stuff,
): u64 {
    0u64
} 

#[spec(prove, ignore_abort)]
public fun foo_spec(    
    self: &mut Stuff,
): u64 {

    // let dummy: Option<u64> = option::some(0u64);
    let result = self.foo();

    result
}