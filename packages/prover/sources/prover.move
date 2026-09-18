module prover::prover;

#[mode(spec), ext(spec_only)]
native public fun requires(p: bool);
#[mode(spec), ext(spec_only)]
native public fun ensures(p: bool);
#[mode(spec), ext(spec_only)]
native public fun asserts(p: bool);
#[mode(spec), ext(spec_only)]
native public fun asserts_of(name: vector<u8>): bool;

/// Emits `assume {:split_here} true;` — cuts the VC at this point.
#[mode(spec), ext(spec_only)]
native public fun boogie_split_here();

/// Emits `assume {:focus} true;` — splits into "through here" vs "not through here" VCs.
#[mode(spec), ext(spec_only)]
native public fun boogie_focus();

/// Annotates the next `if` with `{:allow_path_isolation}`.
/// Use with `boogie_opt = b"{:isolate_paths}"` on the spec.
#[mode(spec), ext(spec_only)]
native public fun boogie_allow_path_isolation();

#[mode(spec), ext(spec_only)]
public macro fun invariant($invariants: ||) {
    invariant_begin();
    $invariants();
    invariant_end();
}

public fun implies(p: bool, q: bool): bool {
    !p || q
}

#[mode(spec), ext(spec_only)]
native public fun invariant_begin();
#[mode(spec), ext(spec_only)]
native public fun invariant_end();

#[mode(spec), ext(spec_only)]
native public fun val<T>(x: &T): T;
#[mode(spec), ext(spec)]
fun val_spec<T>(x: &T): T {
    let result = val(x);

    ensures(result == x);

    result
}

#[mode(spec), ext(spec_only)]
native public fun ref<T>(x: T): &T;
#[mode(spec), ext(spec)]
fun ref_spec<T>(x: T): &T {
    let old_x = val(&x);

    let result = ref(x);

    ensures(result == old_x);
    drop(old_x);

    result
}

#[mode(spec), ext(spec_only)]
native public fun drop<T>(x: T);
#[mode(spec), ext(spec)]
fun drop_spec<T>(x: T) {
    drop(x);
}

#[mode(spec), ext(spec_only)]
public macro fun clone<$T>($x: &$T): &$T {
    ref(val($x))
}

#[mode(spec), ext(spec_only)]
native public fun fresh<T>(): T;
#[mode(spec), ext(spec)]
fun fresh_spec<T>(): T {
    fresh()
}

#[mode(spec), ext(spec_only)]
#[allow(unused)]
native fun type_inv<T>(x: &T): bool;

#[mode(spec), ext(spec_only)]
public native fun begin_forall_lambda<T>(): &T;
#[mode(spec), ext(spec_only)]
public native fun end_forall_lambda(): bool;
#[mode(spec), ext(spec_only)]
public native fun begin_exists_lambda<T>(): &T;
#[mode(spec), ext(spec_only)]
public native fun end_exists_lambda(): bool;

#[mode(spec), ext(spec_only)]
public macro fun forall<$T>($f: |&$T| -> bool): bool {
    let x: &$T = begin_forall_lambda<$T>();
    let _ = $f(x);
    end_forall_lambda()
}

#[mode(spec), ext(spec_only)]
public macro fun exists<$T>($f: |&$T| -> bool): bool {
    let x: &$T = begin_exists_lambda<$T>();
    let _ = $f(x);
    end_exists_lambda()
}
