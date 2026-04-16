module prover::prover;

#[spec_only]
native public fun requires(p: bool);
#[spec_only]
native public fun ensures(p: bool);
#[spec_only]
native public fun asserts(p: bool);
#[spec_only]
native public fun asserts_of(name: vector<u8>): bool;

/// Forces Boogie to split the verification condition at this point. The
/// bytecode translator emits `assert {:split_here} true;`, which causes
/// Boogie to create two smaller VCs (before and after the split) instead
/// of one large one. Useful when a spec's VC is too heavy for Z3 to solve
/// whole; splitting often turns a timeout into a few seconds per piece.
#[spec_only]
native public fun split_here();
#[spec_only]
public macro fun invariant($invariants: ||) {
    invariant_begin();
    $invariants();
    invariant_end();
}

public fun implies(p: bool, q: bool): bool {
    !p || q
}

#[spec_only]
native public fun invariant_begin();
#[spec_only]
native public fun invariant_end();

#[spec_only]
native public fun val<T>(x: &T): T;
#[spec]
fun val_spec<T>(x: &T): T {
    let result = val(x);

    ensures(result == x);

    result
}

#[spec_only]
native public fun ref<T>(x: T): &T;
#[spec]
fun ref_spec<T>(x: T): &T {
    let old_x = val(&x);

    let result = ref(x);

    ensures(result == old_x);
    drop(old_x);

    result
}

#[spec_only]
native public fun drop<T>(x: T);
#[spec]
fun drop_spec<T>(x: T) {
    drop(x);
}

#[spec_only]
public macro fun clone<$T>($x: &$T): &$T {
    ref(val($x))
}

#[spec_only]
native public fun fresh<T>(): T;
#[spec]
fun fresh_spec<T>(): T {
    fresh()
}

#[spec_only]
#[allow(unused)]
native fun type_inv<T>(x: &T): bool;

#[spec_only]
public native fun begin_forall_lambda<T>(): &T;
#[spec_only]
public native fun end_forall_lambda(): bool;
#[spec_only]
public native fun begin_exists_lambda<T>(): &T;
#[spec_only]
public native fun end_exists_lambda(): bool;

#[spec_only]
public macro fun forall<$T>($f: |&$T| -> bool): bool {
    let x: &$T = begin_forall_lambda<$T>();
    let _ = $f(x);
    end_forall_lambda()
}

#[spec_only]
public macro fun exists<$T>($f: |&$T| -> bool): bool {
    let x: &$T = begin_exists_lambda<$T>();
    let _ = $f(x);
    end_exists_lambda()
}
