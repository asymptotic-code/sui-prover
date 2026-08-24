module prover::log;

#[mode(spec)]
public native fun text(x: vector<u8>);

#[mode(spec)]
public native fun var<T>(x: &T);

#[mode(spec)]
public native fun ghost<T, U>();
