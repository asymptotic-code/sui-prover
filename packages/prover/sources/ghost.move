module prover::ghost;

#[mode(spec)]
use prover::prover;

#[mode(spec)]
public native fun global<T, U>(): &U;

#[mode(spec)]
public native fun set<T, U>(x: &U);

#[spec]
public fun set_spec<T, U>(x: &U) {
  declare_global_mut<T, U>();
  set<T, U>(x);
  prover::ensures(global<T, U>() == x);
}

#[mode(spec)]
public native fun borrow_mut<T, U>(): &mut U;

#[mode(spec)]
public native fun declare_global<T, U>();
#[mode(spec)]
public native fun declare_global_mut<T, U>();

#[mode(spec)]
#[allow(unused)]
native fun havoc_global<T, U>();
