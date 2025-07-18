module 0x42::ghost_tests;

use sui::vec_map::VecMap;

public struct Stuff has copy, drop, store {
    key_value_map: VecMap<Key, Value>,
}

public struct Key has copy, drop, store {
    key: u32,
}

public struct Value has copy, drop, store {
    value: u64,
    complex: VecMap<u32, VecMap<u32, vector<u32>>>,
}

public fun foo(self: &mut Stuff,
    key: u32
): bool {
    let mut value = self.get_value(key);
    true
}


fun get_value(self: &Stuff, key: u32): Option<Value> {
    let key = Key { key };
    self.key_value_map.try_get(&key)
}

#[spec(prove, ignore_abort)]
public fun foo_spec(
    self: &mut Stuff,
    key: u32
    ): bool {
        
    let res = self.foo(key);

    res
}
