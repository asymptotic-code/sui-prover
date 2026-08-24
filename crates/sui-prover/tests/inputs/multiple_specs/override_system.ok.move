module 0x42::foo_specs;
#[mode(spec)]
use prover::prover::ensures;
#[mode(spec)]
use prover::ghost;
#[mode(spec)]
use sui::transfer::{transfer, transfer_impl};

public struct Foo has key {
  id: UID
}

public struct CustomGlobal {}

#[spec(target = sui::transfer::transfer_impl)]
fun transfer_impl_spec<T: key>(obj: T, recipient: address) {
  ghost::declare_global_mut<CustomGlobal, bool>();
  transfer_impl(obj, recipient);
  ensures(ghost::global<CustomGlobal, bool>() == true);
}

public fun foo(obj: Foo, recipient: address) {
  transfer(obj, recipient);
}

#[spec(prove)]
public fun foo_spec(obj: Foo, recipient: address) {
  ghost::declare_global_mut<CustomGlobal, bool>();
  foo(obj, recipient);
  ensures(ghost::global<CustomGlobal, bool>() == true);
}

// Should not fail because we overrided system spec
