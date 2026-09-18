module prover::log;

#[mode(spec), ext(spec_only)]
public native fun text(x: vector<u8>);

#[mode(spec), ext(spec_only)]
public native fun var<T>(x: &T);

#[mode(spec), ext(spec_only)]
public native fun ghost<T, U>();
