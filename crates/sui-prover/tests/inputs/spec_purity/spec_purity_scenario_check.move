// should not trigger non-pure error
module 0x42::foo;

fun foo(x: &mut u64) {
  *x = *x + 1;
}

#[mode(spec)]
use prover::prover::ensures;

#[spec(prove)]
fun bar_spec() {
  let mut x = 0;
  foo(&mut x);
  ensures(x == 1);
}
