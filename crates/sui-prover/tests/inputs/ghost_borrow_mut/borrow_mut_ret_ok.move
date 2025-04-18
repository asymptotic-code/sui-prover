module 0x42::foo;

use prover::prover::ensures;
use prover::ghost;

public struct GhostStruct {}

fun foo(): &mut bool {
  ghost::borrow_mut<GhostStruct, bool>()
}

#[spec(prove)]
fun ghost_borrow_mut_spec() {
  ghost::declare_global_mut<GhostStruct, bool>();
  let ghost_ref = foo();
  *ghost_ref = true;
  ensures(ghost::global<GhostStruct, bool>() == true);
}
