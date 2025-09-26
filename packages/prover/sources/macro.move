module prover::macro;

#[spec_only]
use std::integer::Integer;
#[spec_only]
use std::option::Option;

#[spec_only]
public native fun begin_forall_lambda<T>(): T;
#[spec_only]
public native fun end_forall_lambda(): bool;
#[spec_only]
public native fun begin_exists_lambda<T>(): T;
#[spec_only]
public native fun end_exists_lambda(): bool;

#[spec_only]
public native fun begin_map_lambda<T>(v: &vector<T>): T;
#[spec_only]
public native fun end_map_lambda<T>(): &vector<T>;
#[spec_only]
public native fun begin_filter_lambda<T>(v: &vector<T>): T;
#[spec_only]
public native fun end_filter_lambda<T>(): &vector<T>;
#[spec_only]
public native fun begin_find_lambda<T>(v: &vector<T>): T;
#[spec_only]
public native fun end_find_lambda<T>(): &Option<T>;
#[spec_only]
public native fun begin_find_index_lambda<T>(v: &vector<T>): T;
#[spec_only]
public native fun end_find_index_lambda(): Option<u64>;
#[spec_only]
public native fun begin_find_indices_lambda<T>(v: &vector<T>): T;
#[spec_only]
public native fun end_find_indices_lambda(): vector<u64>;
#[spec_only]
public native fun begin_count_lambda<T>(v: &vector<T>): T;
#[spec_only]
public native fun end_count_lambda(): u64;
#[spec_only]
public native fun begin_any_lambda<T>(v: &vector<T>): T;
#[spec_only]
public native fun end_any_lambda(): bool;
#[spec_only]
public native fun begin_all_lambda<T>(v: &vector<T>): T;
#[spec_only]
public native fun end_all_lambda(): bool;
#[spec_only]
public native fun begin_sum_map_lambda<T>(v: &vector<T>): T;
#[spec_only]
public native fun end_sum_map_lambda<T>(): Integer;

#[spec_only]
public native fun sum<T>(v: &vector<T>): Integer;

#[spec_only]
public native fun slice<T>(v: &vector<T>, start: u64, end: u64): &vector<T>;

// simple macro patterns
#[spec_only]
public macro fun forall<$T>($f: |&$T| -> bool): bool {
    let x: $T = begin_forall_lambda<$T>();
    let _ = $f(&x);
    end_forall_lambda()
}

#[spec_only]
public macro fun exists<$T>($f: |&$T| -> bool): bool {
    let x: $T = begin_exists_lambda<$T>();
    let _ = $f(&x);
    end_exists_lambda()
}

// advanced macros patterns over vectors
#[spec_only]
public macro fun map<$T, $U>($v: &vector<$T>, $f: |&$T| -> $U): &vector<$U> {
    let v = $v;
    let x: $T = begin_map_lambda<$T>(v);
    let _ = $f(&x);
    end_map_lambda<$U>()
}

#[spec_only]
public macro fun filter<$T>($v: &vector<$T>, $f: |&$T| -> bool): &vector<$T> {
    let v = $v;
    let x: $T = begin_filter_lambda<$T>(v);
    let _ = $f(&x);
    end_filter_lambda<$T>()
}

#[spec_only]
public macro fun find<$T>($v: &vector<$T>, $f: |&$T| -> bool): &Option<$T> {
    let v = $v;
    let x: $T = begin_find_lambda<$T>(v);
    let _ = $f(&x);
    end_find_lambda<$T>()
}

#[spec_only]
public macro fun find_index<$T>($v: &vector<$T>, $f: |&$T| -> bool): Option<u64> {
    let v = $v;
    let x: $T = begin_find_index_lambda<$T>(v);
    let _ = $f(&x);
    end_find_index_lambda()
}

#[spec_only]
public macro fun find_indices<$T>($v: &vector<$T>, $f: |&$T| -> bool): vector<u64> {
    let v = $v;
    let x: $T = begin_find_indices_lambda<$T>(v);
    let _ = $f(&x);
    end_find_indices_lambda()
}

#[spec_only]
public macro fun count<$T>($v: &vector<$T>, $f: |&$T| -> bool): u64 {
    let v = $v;
    let x: $T = begin_count_lambda<$T>(v);
    let _ = $f(&x);
    end_count_lambda()
}

#[spec_only]
public macro fun any<$T>($v: &vector<$T>, $f: |&$T| -> bool): bool {
    let v = $v;
    let x: $T = begin_any_lambda<$T>(v);
    let _ = $f(&x);
    end_any_lambda()
}

#[spec_only]
public macro fun all<$T>($v: &vector<$T>, $f: |&$T| -> bool): bool {
    let v = $v;
    let x: $T = begin_all_lambda<$T>(v);
    let _ = $f(&x);
    end_all_lambda()
}

#[spec_only]
public macro fun sum_map<$T, $U>($v: &vector<$T>, $f: |&$T| -> $U): Integer {
    let v = $v;
    let x: $T = begin_sum_map_lambda<$T>(v);
    let _ = $f(&x);
    end_sum_map_lambda<$U>()
}
