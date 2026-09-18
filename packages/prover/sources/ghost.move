module prover::ghost;

#[mode(spec), ext(spec_only)]
use prover::prover;

#[mode(spec), ext(spec_only)]
public native fun global<T, U>(): &U;

#[mode(spec), ext(spec_only)]
public native fun set<T, U>(x: &U);

#[mode(spec), ext(spec)]
public fun set_spec<T, U>(x: &U) {
  declare_global_mut<T, U>();
  set<T, U>(x);
  prover::ensures(global<T, U>() == x);
}

#[mode(spec), ext(spec_only)]
public native fun borrow_mut<T, U>(): &mut U;

#[mode(spec), ext(spec_only)]
public native fun declare_global<T, U>();
#[mode(spec), ext(spec_only)]
public native fun declare_global_mut<T, U>();

#[mode(spec), ext(spec_only)]
#[allow(unused)]
native fun havoc_global<T, U>();
