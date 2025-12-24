module prover::vector_iter;

#[spec_only]
use std::integer::Integer;
#[spec_only]
use std::option::Option;

#[spec_only]
public native fun begin_map_lambda<T>(v: &vector<T>): &T;
#[spec_only]
public native fun begin_map_range_lambda<T>(v: &vector<T>, start: u64, end: u64): &T;
#[spec_only]
public native fun end_map_lambda<T>(): &vector<T>;
#[spec_only]
public native fun begin_filter_lambda<T>(v: &vector<T>): &T;
#[spec_only]
public native fun begin_filter_range_lambda<T>(v: &vector<T>, start: u64, end: u64): &T;
#[spec_only]
public native fun end_filter_lambda<T>(): &vector<T>;
#[spec_only]
public native fun begin_find_lambda<T>(v: &vector<T>): &T;
#[spec_only]
public native fun begin_find_range_lambda<T>(v: &vector<T>, start: u64, end: u64): &T;
#[spec_only]
public native fun end_find_lambda<T>(): &Option<T>;
#[spec_only]
public native fun begin_find_index_lambda<T>(v: &vector<T>): &T;
#[spec_only]
public native fun begin_find_index_range_lambda<T>(v: &vector<T>, start: u64, end: u64): &T;
#[spec_only]
public native fun end_find_index_lambda(): Option<u64>;
#[spec_only]
public native fun begin_find_indices_lambda<T>(v: &vector<T>): &T;
#[spec_only]
public native fun begin_find_indices_range_lambda<T>(v: &vector<T>, start: u64, end: u64): &T;
#[spec_only]
public native fun end_find_indices_lambda(): vector<u64>;
#[spec_only]
public native fun begin_count_lambda<T>(v: &vector<T>): &T;
#[spec_only]
public native fun begin_count_range_lambda<T>(v: &vector<T>, start: u64, end: u64): &T;
#[spec_only]
public native fun end_count_lambda(): u64;
#[spec_only]
public native fun begin_any_lambda<T>(v: &vector<T>): &T;
#[spec_only]
public native fun begin_any_range_lambda<T>(v: &vector<T>, start: u64, end: u64): &T;
#[spec_only]
public native fun end_any_lambda(): bool;
#[spec_only]
public native fun begin_all_lambda<T>(v: &vector<T>): &T;
#[spec_only]
public native fun begin_all_range_lambda<T>(v: &vector<T>, start: u64, end: u64): &T;
#[spec_only]
public native fun end_all_lambda(): bool;
#[spec_only]
public native fun begin_sum_map_lambda<T>(v: &vector<T>): &T;
#[spec_only]
public native fun begin_sum_map_range_lambda<T>(v: &vector<T>, start: u64, end: u64): &T;
#[spec_only]
public native fun end_sum_map_lambda<T>(): Integer;
#[spec_only]
public native fun begin_range_map_lambda(start: u64, end: u64): u64;
#[spec_only]
public native fun end_range_map_lambda<T>(): &vector<T>;

#[spec_only]
public native fun range(start: u64, end: u64): &vector<u64>;

#[spec_only]
public native fun sum<T>(v: &vector<T>): Integer;

#[spec_only]
public native fun sum_range<T>(v: &vector<T>, start: u64, end: u64): Integer;

#[spec_only]
public native fun slice<T>(v: &vector<T>, start: u64, end: u64): &vector<T>;

// advanced macros patterns over vectors
#[spec_only]
public macro fun map<$T, $U>($v: &vector<$T>, $f: |&$T| -> $U): &vector<$U> {
    let v = $v;
    let x: &$T = begin_map_lambda<$T>(v);
    let _ = $f(x);
    end_map_lambda<$U>()
}

#[spec_only]
public macro fun filter<$T>($v: &vector<$T>, $f: |&$T| -> bool): &vector<$T> {
    let v = $v;
    let x: &$T = begin_filter_lambda<$T>(v);
    let _ = $f(x);
    end_filter_lambda<$T>()
}

#[spec_only]
public macro fun find<$T>($v: &vector<$T>, $f: |&$T| -> bool): &Option<$T> {
    let v = $v;
    let x: &$T = begin_find_lambda<$T>(v);
    let _ = $f(x);
    end_find_lambda<$T>()
}

#[spec_only]
public macro fun find_index<$T>($v: &vector<$T>, $f: |&$T| -> bool): Option<u64> {
    let v = $v;
    let x: &$T = begin_find_index_lambda<$T>(v);
    let _ = $f(x);
    end_find_index_lambda()
}

#[spec_only]
public macro fun find_indices<$T>($v: &vector<$T>, $f: |&$T| -> bool): vector<u64> {
    let v = $v;
    let x: &$T = begin_find_indices_lambda<$T>(v);
    let _ = $f(x);
    end_find_indices_lambda()
}

#[spec_only]
public macro fun count<$T>($v: &vector<$T>, $f: |&$T| -> bool): u64 {
    let v = $v;
    let x: &$T = begin_count_lambda<$T>(v);
    let _ = $f(x);
    end_count_lambda()
}

#[spec_only]
public macro fun any<$T>($v: &vector<$T>, $f: |&$T| -> bool): bool {
    let v = $v;
    let x: &$T = begin_any_lambda<$T>(v);
    let _ = $f(x);
    end_any_lambda()
}

#[spec_only]
public macro fun all<$T>($v: &vector<$T>, $f: |&$T| -> bool): bool {
    let v = $v;
    let x: &$T = begin_all_lambda<$T>(v);
    let _ = $f(x);
    end_all_lambda()
}

#[spec_only]
public macro fun sum_map<$T, $U>($v: &vector<$T>, $f: |&$T| -> $U): Integer {
    let v = $v;
    let x: &$T = begin_sum_map_lambda<$T>(v);
    let _ = $f(x);
    end_sum_map_lambda<$U>()
}

// advanced range versions
#[spec_only]
public macro fun map_range<$T, $U>($v: &vector<$T>, $start: u64, $end: u64, $f: |&$T| -> $U): &vector<$U> {
    let v = $v;
    let x: &$T = begin_map_range_lambda<$T>(v, $start, $end);
    let _ = $f(x);
    end_map_lambda<$U>()
}

#[spec_only]
public macro fun filter_range<$T>($v: &vector<$T>, $start: u64, $end: u64, $f: |&$T| -> bool): &vector<$T> {
    let v = $v;
    let x: &$T = begin_filter_range_lambda<$T>(v, $start, $end);
    let _ = $f(x);
    end_filter_lambda<$T>()
}

#[spec_only]
public macro fun find_range<$T>($v: &vector<$T>, $start: u64, $end: u64, $f: |&$T| -> bool): &Option<$T> {
    let v = $v;
    let x: &$T = begin_find_range_lambda<$T>(v, $start, $end);
    let _ = $f(x);
    end_find_lambda<$T>()
}

#[spec_only]
public macro fun find_index_range<$T>($v: &vector<$T>, $start: u64, $end: u64, $f: |&$T| -> bool): Option<u64> {
    let v = $v;
    let x: &$T = begin_find_index_range_lambda<$T>(v, $start, $end);
    let _ = $f(x);
    end_find_index_lambda()
}

#[spec_only]
public macro fun find_indices_range<$T>($v: &vector<$T>, $start: u64, $end: u64, $f: |&$T| -> bool): vector<u64> {
    let v = $v;
    let x: &$T = begin_find_indices_range_lambda<$T>(v, $start, $end);
    let _ = $f(x);
    end_find_indices_lambda()
}

#[spec_only]
public macro fun count_range<$T>($v: &vector<$T>, $start: u64, $end: u64, $f: |&$T| -> bool): u64 {
    let v = $v;
    let x: &$T = begin_count_range_lambda<$T>(v, $start, $end);
    let _ = $f(x);
    end_count_lambda()
}

#[spec_only]
public macro fun any_range<$T>($v: &vector<$T>, $start: u64, $end: u64, $f: |&$T| -> bool): bool {
    let v = $v;
    let x: &$T = begin_any_range_lambda<$T>(v, $start, $end);
    let _ = $f(x);
    end_any_lambda()
}

#[spec_only]
public macro fun all_range<$T>($v: &vector<$T>, $start: u64, $end: u64, $f: |&$T| -> bool): bool {
    let v = $v;
    let x: &$T = begin_all_range_lambda<$T>(v, $start, $end);
    let _ = $f(x);
    end_all_lambda()
}

#[spec_only]
public macro fun sum_map_range<$T, $U>($v: &vector<$T>, $start: u64, $end: u64, $f: |&$T| -> $U): Integer {
    let v = $v;
    let x: &$T = begin_sum_map_range_lambda<$T>(v, $start, $end);
    let _ = $f(x);
    end_sum_map_lambda<$U>()
}

#[spec_only]
public macro fun range_map<$T>($start: u64, $end: u64, $f: |u64| -> $T): &vector<$T> {
    let x: u64 = begin_range_map_lambda($start, $end);
    let _ = $f(x);
    end_range_map_lambda<$T>()
}
