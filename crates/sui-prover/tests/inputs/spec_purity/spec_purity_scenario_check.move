// should not trigger non-pure error
module 0x42::foo;

fun foo(x: &mut u64) {
  *x = *x + 1;
}

#[mode(spec), ext(spec_only)]
use prover::prover::ensures;

#[mode(spec), ext(spec(prove))]
fun bar_spec() {
  let mut x = 0;
  foo(&mut x);
  ensures(x == 1);
}
