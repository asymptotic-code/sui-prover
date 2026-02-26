{# Copyright (c) The Diem Core Contributors
   SPDX-License-Identifier: Apache-2.0
#}

{# Option
   =======
#}

{% macro option_module(instance) %}
{%- set T = instance.name -%}
{%- set S = "'" ~ instance.suffix ~ "'" -%}

function $IsValid'$1_option_Option{{S}}'(opt: $1_option_Option{{S}}): bool {
    $IsValid'vec{{S}}'(opt->$vec) &&
    (LenVec(opt->$vec) == 0 || LenVec(opt->$vec) == 1)
}

{% endmacro option_module %}

{# Vectors
   =======
#}

{% macro vector_module(instance) %}
{%- set S = "'" ~ instance.suffix ~ "'" -%}
{%- set T = instance.name -%}
{%- if options.native_equality -%}
{# Whole vector has native equality #}
function {:inline} $IsEqual'vec{{S}}'(v1: Vec ({{T}}), v2: Vec ({{T}})): bool {
    v1 == v2
}
{%- else -%}
// Not inlined. It appears faster this way.
function $IsEqual'vec{{S}}'(v1: Vec ({{T}}), v2: Vec ({{T}})): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual{{S}}(ReadVec(v1, i), ReadVec(v2, i)))
}
{%- endif %}

// Not inlined.
function $IsPrefix'vec{{S}}'(v: Vec ({{T}}), prefix: Vec ({{T}})): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual{{S}}(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec{{S}}'(v: Vec ({{T}}), suffix: Vec ({{T}})): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual{{S}}(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec{{S}}'(v: Vec ({{T}})): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid{{S}}(ReadVec(v, i)))
}

// Not inlined.
procedure {:inline 1} $0_prover_type_inv'vec{{S}}'(v: Vec ({{T}})) returns (res: bool) {
    res := true;
}

{# TODO: there is an issue with existential quantifier instantiation if we use the native
   functions here without the $IsValid'u64' tag.
#}
{%- if false and instance.has_native_equality -%}
{# Vector elements have native equality #}
function {:inline} $ContainsVec{{S}}(v: Vec ({{T}}), e: {{T}}): bool {
    ContainsVec(v, e)
}

function {:inline} $IndexOfVec{{S}}(v: Vec ({{T}}), e: {{T}}): int {
    IndexOfVec(v, e)
}
{% else %}
function {:inline} $ContainsVec{{S}}(v: Vec ({{T}}), e: {{T}}): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual{{S}}(ReadVec(v, i), e))
}

function $IndexOfVec{{S}}(v: Vec ({{T}}), e: {{T}}): int;
axiom (forall v: Vec ({{T}}), e: {{T}}:: {$IndexOfVec{{S}}(v, e)}
    (var i := $IndexOfVec{{S}}(v, e);
     if (!$ContainsVec{{S}}(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual{{S}}(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual{{S}}(ReadVec(v, j), e))));
{% endif %}

function {:inline} $RangeVec{{S}}(v: Vec ({{T}})): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec{{S}}(): Vec ({{T}}) {
    EmptyVec()
}

function {:inline} $1_vector_empty{{S}}(): Vec ({{T}}) {
    EmptyVec()
}

function {:inline} $1_vector_is_empty{{S}}(v: Vec ({{T}})): bool {
    IsEmptyVec(v)
}

function {:inline} $1_vector_push_back{{S}}(m: $Mutation (Vec ({{T}})), val: {{T}}): $Mutation (Vec ({{T}})) {
    $UpdateMutation(m, ExtendVec($Dereference(m), val))
}

function {:inline} $1_vector_$push_back{{S}}(v: Vec ({{T}}), val: {{T}}): Vec ({{T}}) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back{{S}}(m: $Mutation (Vec ({{T}}))) returns (e: {{T}}, m': $Mutation (Vec ({{T}}))) {
    var v: Vec ({{T}});
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

function {:inline} $1_vector_append{{S}}(m: $Mutation (Vec ({{T}})), other: Vec ({{T}})): $Mutation (Vec ({{T}})) {
    $UpdateMutation(m, ConcatVec($Dereference(m), other))
}

function {:inline} $1_vector_reverse{{S}}(m: $Mutation (Vec ({{T}}))): $Mutation (Vec ({{T}})) {
    $UpdateMutation(m, ReverseVec($Dereference(m)))
}

function {:inline} $1_vector_reverse_append{{S}}(m: $Mutation (Vec ({{T}})), other: Vec ({{T}})): $Mutation (Vec ({{T}})) {
    $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)))
}

procedure {:inline 1} $1_vector_trim_reverse{{S}}(m: $Mutation (Vec ({{T}})), new_len: int) returns (v: (Vec ({{T}})), m': $Mutation (Vec ({{T}}))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim{{S}}(m: $Mutation (Vec ({{T}})), new_len: int) returns (v: (Vec ({{T}})), m': $Mutation (Vec ({{T}}))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice{{S}}(m: $Mutation (Vec ({{T}})), left: int, right: int) returns (m': $Mutation (Vec ({{T}}))) {
    var left_vec: Vec ({{T}});
    var mid_vec: Vec ({{T}});
    var right_vec: Vec ({{T}});
    var v: Vec ({{T}});
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate{{S}}(m: $Mutation (Vec ({{T}})), rot: int) returns (n: int, m': $Mutation (Vec ({{T}}))) {
    var v: Vec ({{T}});
    var len: int;
    var left_vec: Vec ({{T}});
    var right_vec: Vec ({{T}});
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice{{S}}(m: $Mutation (Vec ({{T}})), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec ({{T}}))) {
    var left_vec: Vec ({{T}});
    var mid_vec: Vec ({{T}});
    var right_vec: Vec ({{T}});
    var mid_left_vec: Vec ({{T}});
    var mid_right_vec: Vec ({{T}});
    var v: Vec ({{T}});
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert{{S}}(m: $Mutation (Vec ({{T}})), i: int, e: {{T}}) returns (m': $Mutation (Vec ({{T}}))) {
    var left_vec: Vec ({{T}});
    var right_vec: Vec ({{T}});
    var v: Vec ({{T}});
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

function {:inline} $1_vector_length{{S}}(v: Vec ({{T}})): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow{{S}}(v: Vec ({{T}}), i: int) returns (dst: {{T}}) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_borrow{{S}}$pure(v: Vec ({{T}}), i: int): {{T}} {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut{{S}}(m: $Mutation (Vec ({{T}})), index: int)
returns (dst: $Mutation ({{T}}), m': $Mutation (Vec ({{T}})))
{
    var v: Vec ({{T}});
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

procedure {:inline 1} $1_vector_destroy_empty{{S}}(v: Vec ({{T}})) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap{{S}}(m: $Mutation (Vec ({{T}})), i: int, j: int) returns (m': $Mutation (Vec ({{T}})))
{
    var v: Vec ({{T}});
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap{{S}}(v: Vec ({{T}}), i: int, j: int): Vec ({{T}}) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove{{S}}(m: $Mutation (Vec ({{T}})), i: int) returns (e: {{T}}, m': $Mutation (Vec ({{T}})))
{
    var v: Vec ({{T}});

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove{{S}}(m: $Mutation (Vec ({{T}})), i: int) returns (e: {{T}}, m': $Mutation (Vec ({{T}})))
{
    var len: int;
    var v: Vec ({{T}});

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

function {:inline} $1_vector_contains{{S}}(v: Vec ({{T}}), e: {{T}}): bool {
    $ContainsVec{{S}}(v, e)
}

function {:inline} $1_vector_singleton{{S}}(e: {{T}}): Vec ({{T}}) {
    MakeVec1(e)
}

procedure {:inline 1}
$1_vector_index_of{{S}}(v: Vec ({{T}}), e: {{T}}) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec{{S}}(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}

procedure {:inline 1} $1_vector_take{{S}}(v: Vec ({{T}}), n: int) returns (res: Vec ({{T}})) {
    var len: int;
    len := LenVec(v);
    if (n > len) {
        call $ExecFailureAbort();
        return;
    }
    if (n == len) {
        res := v;
    } else {
        res := SliceVec(v, 0, n);
    }
}

function {:inline} $1_vector_$take{{S}}(v: Vec ({{T}}), n: int): Vec ({{T}}) {
    (if n >= LenVec(v) then v else SliceVec(v, 0, n))
}

procedure {:inline 1} $1_vector_skip{{S}}(v: Vec ({{T}}), n: int) returns (res: Vec ({{T}})) {
    var len: int;
    len := LenVec(v);
    if (n >= len) {
        res := EmptyVec();
    } else {
        res := SliceVec(v, n, len);
    }
}

function {:inline} $1_vector_$skip{{S}}(v: Vec ({{T}}), n: int): Vec ({{T}}) {
    (if n >= LenVec(v) then EmptyVec() else SliceVec(v, n, LenVec(v)))
}

function {:inline} $0_vector_iter_slice{{S}}(v: Vec ({{T}}), start: int, end: int): Vec ({{T}}) {
    SliceVec(v, start, end)
}

{%- if instance.is_number -%}
{%- if include_vec_sum -%}

function $0_vec_$sum{{S}}(v: Vec ({{T}}), start: int, end: int): {{T}};

{%- if instance.is_bv -%}
{# Different axioms for bit vectors #}

// the sum over an empty range is zero
axiom (forall v: Vec ({{T}}), start: int, end: int ::
      { $0_vec_$sum{{S}}(v, start, end)}
   (start >= end ==> $0_vec_$sum{{S}}(v, start, end) == 0bv{{instance.bit_width}}));

// the sum of a range can be split in two
axiom (forall v: Vec ({{T}}), a: int, b: int, c: int, d: int ::
  { $0_vec_$sum{{S}}(v, a, b), $0_vec_$sum{{S}}(v, c, d) }
  0 <= a && a <= b && b == c && c <= d && d <= LenVec(v)  ==>
    $Add'Bv{{instance.bit_width}}'($0_vec_$sum{{S}}(v, a, b), $0_vec_$sum{{S}}(v, c, d)) == $0_vec_$sum{{S}}(v, a, d)) ;

// the sum over a singleton range is the vector element there
axiom (forall v: Vec ({{T}}), a: int, x: int, y: int ::
  { $0_vec_$sum{{S}}(v, x, y), v->v[a] } // in a proof involving 0_vec_sum(v,...) and v[a]
  0 <= a && a < LenVec(v) ==> $0_vec_$sum{{S}}(v, a, a+1) == v->v[a]);

// for vectors nested ranges have sums bounded by the larger
axiom (forall v: Vec ({{T}}), a: int, b: int, c: int, d: int ::
  { $0_vec_$sum{{S}}(v, a, d), $0_vec_$sum{{S}}(v, b, c) }
  $IsValid'vec{{S}}'(v) && 0 <= a && a <= b && b <= c && c <= d && d <= LenVec(v)  ==>
    $Le'Bv{{instance.bit_width}}'($0_vec_$sum{{S}}(v, b, c), $0_vec_$sum{{S}}(v, a, d)));

// equal vectors have equal sums over the same range
axiom (forall u: Vec({{T}}), v: Vec({{T}}), from: int, to: int ::
  $IsEqual'vec{{S}}'(u, v) &&
   0 <= from && from <= to && to <= LenVec(u) ==>
   $0_vec_$sum{{S}}(u, from, to) == $0_vec_$sum{{S}}(v, from, to));

{%- else -%}

// the sum over an empty range is zero
axiom (forall v: Vec ({{T}}), start: int, end: int ::
      { $0_vec_$sum{{S}}(v, start, end)}
   (start >= end ==> $0_vec_$sum{{S}}(v, start, end) == 0));

// the sum of a range can be split in two
axiom (forall v: Vec ({{T}}), a: int, b: int, c: int, d: int ::
  { $0_vec_$sum{{S}}(v, a, b), $0_vec_$sum{{S}}(v, c, d) }
  0 <= a && a <= b && b == c && c <= d && d <= LenVec(v)  ==>
    $0_vec_$sum{{S}}(v, a, b) + $0_vec_$sum{{S}}(v, c, d) ==  $0_vec_$sum{{S}}(v, a, d)) ;

// the sum over a singleton range is the vector element there
axiom (forall v: Vec ({{T}}), a: int, x: int, y: int ::
  { $0_vec_$sum{{S}}(v, x, y), v->v[a] } // in a proof involving 0_vec_sum(v,...) and v[a]
  0 <= a && a < LenVec(v)  ==> $0_vec_$sum{{S}}(v, a, a+1) == v->v[a]);

// for vectors nested ranges have sums bounded by the larger
axiom (forall v: Vec ({{T}}), a: int, b: int, c: int, d: int ::
  { $0_vec_$sum{{S}}(v, a, d), $0_vec_$sum{{S}}(v, b, c) }
  $IsValid'vec{{S}}'(v) && 0 <= a && a <= b && b <= c && c <= d && d <= LenVec(v)  ==>
    $0_vec_$sum{{S}}(v, b, c) <= $0_vec_$sum{{S}}(v, a, d));

// equal vectors have equal sums over the same range
axiom (forall u: Vec({{T}}), v: Vec({{T}}), from: int, to: int ::
  $IsEqual'vec{{S}}'(u, v) &&
   0 <= from && from <= to && to <= LenVec(u) ==>
   $0_vec_$sum{{S}}(u, from, to) == $0_vec_$sum{{S}}(v, from, to));

{%- endif %}

function {:inline} $0_vector_iter_sum{{S}}(v: Vec ({{T}})): {{T}} {
    $0_vec_$sum{{S}}(v, 0, LenVec(v))
}

function {:inline} $0_vector_iter_sum_range{{S}}(v: Vec ({{T}}), start: int, end: int): {{T}} {
    $0_vec_$sum{{S}}(v, start, end)
}

{%- endif %}
{%- endif %}

{% endmacro vector_module %}

{# VecSet
   =======
#}

{% macro vec_set_module(instance) %}
{%- set T = instance.name -%}
{%- set S = "'" ~ instance.suffix ~ "'" -%}

procedure {:inline 1} $2_vec_set_get_idx_opt{{S}}(
    s: $2_vec_set_VecSet{{S}},
    e: {{T}}
) returns (res: $1_option_Option'u64') {
    var res0: int;
    res0 := $IndexOfVec{{S}}(s->$contents, e);
    if (res0 >= 0) {
        res := $1_option_Option'u64'(MakeVec1(res0));
    } else {
        res := $1_option_Option'u64'(EmptyVec());
    }
}

function $DisjointVecSet{{S}}(v: Vec ({{T}})): bool {
    (forall i: int, j: int :: {$IsEqual{{S}}(ReadVec(v, i), ReadVec(v, j))}
        InRangeVec(v, i) && InRangeVec(v, j) && i != j ==> !$IsEqual{{S}}(ReadVec(v, i), ReadVec(v, j)))
}

procedure {:inline 1} $2_vec_set_from_keys{{S}}(v: Vec ({{T}})) returns (res: $2_vec_set_VecSet{{S}}) {
    if (!$DisjointVecSet{{S}}(v)) {
        call $Abort(0);
        return;
    }
    res := $2_vec_set_VecSet{{S}}(v);
}

function {:inline} $2_vec_set_contains{{S}}(
    s: $2_vec_set_VecSet{{S}},
    e: {{T}}
): bool {
    $ContainsVec{{S}}(s->$contents, e)
}

procedure {:inline 1} $2_vec_set_remove{{S}}(
    m: $Mutation ($2_vec_set_VecSet{{S}}),
    e: {{T}}
) returns (m': $Mutation ($2_vec_set_VecSet{{S}})) {
    var s: $2_vec_set_VecSet{{S}};
    var v: Vec ({{T}});
    var idx: int;
    s := $Dereference(m);
    v := s->$contents;
    idx := $IndexOfVec{{S}}(v, e);
    if (idx < 0) {
        call $Abort(1); // EKeyDoesNotExist
        return;
    }
    m' := $UpdateMutation(m, $2_vec_set_VecSet{{S}}(RemoveAtVec(v, idx)));
}

{% endmacro vec_set_module %}

{# TableVec
   =======
#}

{% macro table_vec_module(instance) %}
{%- set T = instance.name -%}
{%- set T_S = instance.suffix -%}
{%- set S = "'" ~ instance.suffix ~ "'" -%}

function $IsValid'$2_table_vec_TableVec{{S}}'(s: $2_table_vec_TableVec{{S}}): bool {
    $IsValid'$2_table_Table'u64_{{T_S}}''(s->$contents) &&
    (forall i: int :: (0 <= i && i < LenTable(s->$contents->$contents)) <==> ContainsTable(s->$contents->$contents, $EncodeKey'u64'(i)))
}

{% endmacro table_vec_module %}

{# VecMap
   =======
#}

{% macro vec_map_module(key_instance, value_instance) %}
{%- set K = key_instance.name -%}
{%- set V = value_instance.name -%}
{%- set K_S = "'" ~ key_instance.suffix ~ "'" -%}
{%- set V_S = "'" ~ value_instance.suffix ~ "'" -%}
{%- set S = "'" ~ key_instance.suffix ~ "_" ~ value_instance.suffix ~ "'" -%}

function {:inline} $ContainsVecMap{{S}}(v: Vec ($2_vec_map_Entry{{S}}), k: {{K}}): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual{{K_S}}(ReadVec(v, i)->$key, k))
}

function $IndexOfVecMap{{S}}(v: Vec ($2_vec_map_Entry{{S}}), k: {{K}}): int;
axiom (forall v: Vec ($2_vec_map_Entry{{S}}), k: {{K}} :: {$IndexOfVecMap{{S}}(v, k)}
    (var i := $IndexOfVecMap{{S}}(v, k);
     if (!$ContainsVecMap{{S}}(v, k)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual{{K_S}}(ReadVec(v, i)->$key, k) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual{{K_S}}(ReadVec(v, i)->$key, k))));

function $VecMapKeys{{S}}(v: Vec ($2_vec_map_Entry{{S}})): Vec ({{K}});
axiom (forall v: Vec ($2_vec_map_Entry{{S}}) :: {$VecMapKeys{{S}}(v)}
    (var keys := $VecMapKeys{{S}}(v);
     LenVec(keys) == LenVec(v) &&
     (forall i: int :: InRangeVec(v, i) ==> $IsEqual{{K_S}}(ReadVec(keys, i), ReadVec(v, i)->$key))));

function $VecMapValues{{S}}(v: Vec ($2_vec_map_Entry{{S}})): Vec ({{V}});
axiom (forall v: Vec ($2_vec_map_Entry{{S}}) :: {$VecMapValues{{S}}(v)}
    (var values := $VecMapValues{{S}}(v);
     LenVec(values) == LenVec(v) &&
     (forall i: int :: InRangeVec(v, i) ==> $IsEqual{{V_S}}(ReadVec(values, i), ReadVec(v, i)->$value))));

function {:inline} $2_vec_map_keys{{S}}(m: $2_vec_map_VecMap{{S}}): Vec ({{K}}) {
    $VecMapKeys{{S}}(m->$contents)
}

procedure {:inline 1} $2_vec_map_into_keys_values{{S}}(m: $2_vec_map_VecMap{{S}}) returns (res0: Vec ({{K}}), res1: Vec ({{V}})) {
    res0 := $VecMapKeys{{S}}(m->$contents);
    res1 := $VecMapValues{{S}}(m->$contents);
}

function $DisjointVecMap{{S}}(v: Vec ($2_vec_map_Entry{{S}})): bool {
    (forall i: int, j: int :: {$IsEqual{{K_S}}(ReadVec(v, i)->$key, ReadVec(v, j)->$key)}
        InRangeVec(v, i) && InRangeVec(v, j) && i != j ==> !$IsEqual{{K_S}}(ReadVec(v, i)->$key, ReadVec(v, j)->$key))
}

function $VecMapFromKeysValues{{S}}(keys: Vec ({{K}}), values: Vec ({{V}})): Vec ($2_vec_map_Entry{{S}});
axiom (forall keys: Vec ({{K}}), values: Vec ({{V}}) :: {$VecMapFromKeysValues{{S}}(keys, values)}
    (var entries := $VecMapFromKeysValues{{S}}(keys, values);
     LenVec(entries) == LenVec(keys) &&
     (forall i: int :: InRangeVec(keys, i) ==>
        $IsEqual{{K_S}}(ReadVec(entries, i)->$key, ReadVec(keys, i)) && $IsEqual{{V_S}}(ReadVec(entries, i)->$value, ReadVec(values, i)))));

procedure {:inline 1} $2_vec_map_from_keys_values{{S}}(keys: Vec ({{K}}), values: Vec ({{V}})) returns (res: $2_vec_map_VecMap{{S}}) {
    var entries: Vec ($2_vec_map_Entry{{S}});
    if (LenVec(keys) != LenVec(values)) {
        call $Abort(5);
        return;
    }
    entries := $VecMapFromKeysValues{{S}}(keys, values);
    if (!$DisjointVecMap{{S}}(entries)) {
        call $Abort(0);
        return;
    }
    res := $2_vec_map_VecMap{{S}}(entries);
}

procedure {:inline 1} $2_vec_map_remove{{S}}(m: $Mutation ($2_vec_map_VecMap{{S}}), key: {{K}}) returns (res0: {{K}}, res1: {{V}}, m': $Mutation ($2_vec_map_VecMap{{S}})) {
    var idx: int;
    var entry: $2_vec_map_Entry{{S}};
    var v: Vec ($2_vec_map_Entry{{S}});

    v := $Dereference(m)->$contents;

    idx := $IndexOfVecMap{{S}}(v, key);
    
    if (idx < 0) {
        call $ExecFailureAbort();
        return;
    }
    
    entry := ReadVec(v, idx);
    res0 := entry->$key;
    res1 := entry->$value;

    m' := $UpdateMutation(m, $2_vec_map_VecMap{{S}}(RemoveAtVec(v, idx)));
}

function {:inline} $2_vec_map_contains{{S}}(vm: $2_vec_map_VecMap{{S}}, key: {{K}}): bool {
    $ContainsVecMap{{S}}(vm->$contents, key)
}

procedure {:inline 1} $2_vec_map_get{{S}}(vm: $2_vec_map_VecMap{{S}}, key: {{K}}) returns (res: {{V}}) {
    var idx: int;
    idx := $IndexOfVecMap{{S}}(vm->$contents, key);
    
    if (idx < 0) {
        call $ExecFailureAbort();
        return;
    }

    res := ReadVec(vm->$contents, idx)->$value;
}

procedure {:inline 1} $2_vec_map_get_idx{{S}}(vm: $2_vec_map_VecMap{{S}}, key: {{K}}) returns (idx: int) {
    idx := $IndexOfVecMap{{S}}(vm->$contents, key);
    
    if (idx < 0) {
        call $ExecFailureAbort();
        return;
    }
}

function {:inline} $2_vec_map_get_idx_opt{{S}}(vm: $2_vec_map_VecMap{{S}}, key: {{K}}): $1_option_Option'u64' {
    (var idx := $IndexOfVecMap{{S}}(vm->$contents, key);
     if idx >= 0 then
         $1_option_Option'u64'(MakeVec1(idx))
     else 
         $1_option_Option'u64'(EmptyVec()))
}

{% endmacro vec_map_module %}

{# Tables
   =======
#}

{% macro table_key_encoding(instance) %}
{%- set K = instance.name -%}
{%- set S = "'" ~ instance.suffix ~ "'" -%}

function $EncodeKey{{S}}(k: {{K}}): int;
axiom (
  forall k1, k2: {{K}} :: {$EncodeKey{{S}}(k1), $EncodeKey{{S}}(k2)}
    $IsEqual{{S}}(k1, k2) <==> $EncodeKey{{S}}(k1) == $EncodeKey{{S}}(k2)
);
{% endmacro table_key_encoding %}

{% macro table_is_valid_is_equal(instance) %}
{%- set V = instance.name -%}
{%- set Self = "Table int (" ~ V ~ ")" -%}
{%- set S = "'" ~ "Table" ~ "'" ~ "int" ~ "_" ~ instance.suffix ~ "'" ~ "'" -%}
{%- set SV = "'" ~ instance.suffix ~ "'" -%}

{%- if options.native_equality -%}
function $IsEqual'{{S}}'(t1: {{Self}}, t2: {{Self}}): bool {
    t1 == t2
}
{%- else -%}
function $IsEqual'{{S}}'(t1: {{Self}}, t2: {{Self}}): bool {
    LenTable(t1) == LenTable(t2) &&
    (forall k: int :: ContainsTable(t1, k) <==> ContainsTable(t2, k)) &&
    (forall k: int :: ContainsTable(t1, k) ==> $IsEqual{{SV}}(GetTable(t1, k), GetTable(t2, k))) &&
    (forall k: int :: ContainsTable(t2, k) ==> $IsEqual{{SV}}(GetTable(t1, k), GetTable(t2, k)))
}
{%- endif %}

// Not inlined.
function $IsValid'{{S}}'(t: {{Self}}): bool {
    $IsValid'u64'(LenTable(t)) &&
    (forall i: int:: ContainsTable(t, i) ==> $IsValid{{SV}}(GetTable(t, i)))
}

{% endmacro table_is_valid_is_equal %}

{% macro table_module(impl, instance) %}
{%- set K = instance.0.name -%}
{%- set V = instance.1.name -%}
{%- set Type = impl.struct_name -%}
{%- set Self = "Table int (" ~ V ~ ")" -%}
{%- set S = "'" ~ instance.0.suffix ~ "_" ~ instance.1.suffix ~ "'" -%}
{%- set SV = "'" ~ instance.1.suffix ~ "'" -%}
{%- set ENC = "$EncodeKey'" ~ instance.0.suffix ~ "'" -%}

datatype {{Type}}{{S}} {
    {{Type}}{{S}}($id: $2_object_UID, $contents: {{Self}})
}

function {:inline} $Update'{{Type}}{{S}}'_id(s: {{Type}}{{S}}, x: $2_object_UID): {{Type}}{{S}} {
    {{Type}}{{S}}(x, s->$contents)
}
function {:inline} $Update'{{Type}}{{S}}'_contents(s: {{Type}}{{S}}, x: {{Self}}): {{Type}}{{S}} {
    {{Type}}{{S}}(s->$id, x)
}

{%- if options.native_equality -%}
function $IsEqual'{{Type}}{{S}}'(t1: {{Type}}{{S}}, t2: {{Type}}{{S}}): bool {
    t1 == t2
}
{%- else -%}
function $IsEqual'{{Type}}{{S}}'(t1: {{Type}}{{S}}, t2: {{Type}}{{S}}): bool {
    // TODO use $IsEqual'{{Self}}'(t1->$contents, t2->$contents)
    LenTable(t1->$contents) == LenTable(t2->$contents) &&
    (forall k: int :: ContainsTable(t1->$contents, k) <==> ContainsTable(t2->$contents, k)) &&
    (forall k: int :: ContainsTable(t1->$contents, k) ==> $IsEqual{{SV}}(GetTable(t1->$contents, k), GetTable(t2->$contents, k))) &&
    (forall k: int :: ContainsTable(t2->$contents, k) ==> $IsEqual{{SV}}(GetTable(t1->$contents, k), GetTable(t2->$contents, k)))
}
{%- endif %}

// Not inlined.
function $IsValid'{{Type}}{{S}}'(t: {{Type}}{{S}}): bool {
    // TODO use $IsValid'{{Self}}'(t->$contents)
    $IsValid'u64'(LenTable(t->$contents)) &&
    (forall i: int:: ContainsTable(t->$contents, i) ==> $IsValid{{SV}}(GetTable(t->$contents, i)))
}

{%- if impl.fun_new != "" %}
procedure {:inline 2} {{impl.fun_new}}{{S}}($ctx: $Mutation ($2_tx_context_TxContext))
returns (t: {{Type}}{{S}}, $ctx': $Mutation ($2_tx_context_TxContext)) {
    var uid: $2_object_UID;
    t := {{Type}}{{S}}(uid, EmptyTable());
    $ctx' := $ctx;
}
{%- endif %}

{%- if impl.fun_add != "" %}
procedure {:inline 2} {{impl.fun_add}}{{S}}(m: $Mutation ({{Type}}{{S}}), k: {{K}}, v: {{V}}) returns (m': $Mutation({{Type}}{{S}})) {
    var enc_k: int;
    var t: {{Type}}{{S}};
    enc_k := {{ENC}}(k);
    t := $Dereference(m);
    if (ContainsTable(t->$contents, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 100/*EALREADY_EXISTS*/));
    } else {
        m' := $UpdateMutation(m, $Update'{{Type}}{{S}}'_contents(t, AddTable(t->$contents, enc_k, v)));
    }
}
{%- endif %}

{%- if impl.fun_borrow != "" %}
procedure {:inline 2} {{impl.fun_borrow}}{{S}}(t: {{Type}}{{S}}, k: {{K}}) returns (v: {{V}}) {
    var enc_k: int;
    enc_k := {{ENC}}(k);
    if (!ContainsTable(t->$contents, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t->$contents, {{ENC}}(k));
    }
}
function {:inline} {{impl.fun_borrow}}{{S}}$pure(t: {{Type}}{{S}}, k: {{K}}): {{V}} {
    GetTable(t->$contents, {{ENC}}(k))
}
{%- endif %}

{%- if impl.fun_borrow_mut != "" %}
procedure {:inline 2} {{impl.fun_borrow_mut}}{{S}}(m: $Mutation ({{Type}}{{S}}), k: {{K}})
returns (dst: $Mutation ({{V}}), m': $Mutation ({{Type}}{{S}})) {
    var enc_k: int;
    var t: {{Type}}{{S}};
    enc_k := {{ENC}}(k);
    t := $Dereference(m);
    if (!ContainsTable(t->$contents, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        dst := $Mutation(m->l, ExtendVec(ExtendVec(m->p, 1), enc_k), GetTable(t->$contents, enc_k));
        m' := m;
    }
}
{%- endif %}

{%- if impl.fun_remove != "" %}
procedure {:inline 2} {{impl.fun_remove}}{{S}}(m: $Mutation ({{Type}}{{S}}), k: {{K}})
returns (v: {{V}}, m': $Mutation({{Type}}{{S}})) {
    var enc_k: int;
    var t: {{Type}}{{S}};
    enc_k := {{ENC}}(k);
    t := $Dereference(m);
    if (!ContainsTable(t->$contents, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t->$contents, enc_k);
        m' := $UpdateMutation(m, $Update'{{Type}}{{S}}'_contents(t, RemoveTable(t->$contents, enc_k)));
    }
}
{%- endif %}

{%- if impl.fun_contains != "" %}
function {:inline} {{impl.fun_contains}}{{S}}(t: ({{Type}}{{S}}), k: {{K}}): bool {
    ContainsTable(t->$contents, {{ENC}}(k))
}
{%- endif %}

{%- if impl.fun_length != "" %}
function {:inline} {{impl.fun_length}}{{S}}(t: ({{Type}}{{S}})): int {
    LenTable(t->$contents)
}
{%- endif %}

{%- if impl.fun_is_empty != "" %}
function {:inline} {{impl.fun_is_empty}}{{S}}(t: ({{Type}}{{S}})): bool {
    LenTable(t->$contents) == 0
}
{%- endif %}

{%- if impl.fun_destroy_empty != "" %}
procedure {:inline 2} {{impl.fun_destroy_empty}}{{S}}(t: {{Type}}{{S}}) {
    if (LenTable(t->$contents) != 0) {
        call $Abort($StdError(1/*INVALID_STATE*/, 102/*ENOT_EMPTY*/));
    }
}
{%- endif %}

{%- if impl.fun_drop != "" %}
procedure {:inline 2} {{impl.fun_drop}}{{S}}(t: {{Type}}{{S}}) {}
{%- endif %}

{% endmacro table_module %}


{# Dynamic fields
   =======
#}

{% macro dynamic_field_module(impl, instance) %}
{%- set K = instance.0.name -%}
{%- set V = instance.1.name -%}
{%- set Type = impl.struct_name -%}
{%- set Self = "Table int (" ~ V ~ ")" -%}
{%- set S = "'" ~ instance.0.suffix ~ "_" ~ instance.1.suffix ~ "'" -%}
{%- set SK = "'" ~ instance.0.suffix ~ "_" ~ impl.struct_name ~ "'" -%}
{%- set SV = "'" ~ instance.1.suffix ~ "'" -%}
{%- set DF_S = "'" ~ instance.0.suffix ~ "_" ~ instance.1.suffix ~ "_" ~ impl.struct_name ~ "'" -%}
{%- set ENC = "$EncodeKey'" ~ instance.0.suffix ~ "'" -%}

{%- if impl.fun_add != "" %}
procedure {:inline 2} {{impl.fun_add}}{{DF_S}}(m: $Mutation ({{Type}}), k: {{K}}, v: {{V}}) returns (m': $Mutation({{Type}})) {
    var enc_k: int;
    var t: {{Type}};
    enc_k := {{ENC}}(k);
    t := $Dereference(m);
    if (ContainsTable(t->$dynamic_fields{{S}}, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 100/*EALREADY_EXISTS*/));
    } else {
        m' := $UpdateMutation(m, $Update'{{Type}}'_dynamic_fields{{S}}(t, AddTable(t->$dynamic_fields{{S}}, enc_k, v)));
    }
}
{%- endif %}

{%- if impl.fun_borrow != "" %}
procedure {:inline 2} {{impl.fun_borrow}}{{DF_S}}(t: {{Type}}, k: {{K}}) returns (v: {{V}}) {
    var enc_k: int;
    enc_k := {{ENC}}(k);
    if (!ContainsTable(t->$dynamic_fields{{S}}, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t->$dynamic_fields{{S}}, {{ENC}}(k));
        assume $IsValid{{SV}}(v);
    }
}
function {:inline} {{impl.fun_borrow}}{{DF_S}}$pure(t: {{Type}}, k: {{K}}): {{V}} {
    GetTable(t->$dynamic_fields{{S}}, {{ENC}}(k))
}

// This axiom will be a problem if ever some IsValid predicate is unsatisfiable.
// axiom (forall t: {{Type}}, k: {{K}} :: $IsValid{{SV}}(GetTable(t->$dynamic_fields{{S}}, {{ENC}}(k))));

{%- endif %}

{%- if impl.fun_borrow_mut != "" %}
procedure {:inline 2} {{impl.fun_borrow_mut}}{{DF_S}}(m: $Mutation ({{Type}}), k: {{K}}) returns (dst: $Mutation ({{V}}), m': $Mutation ({{Type}})) {
    var enc_k: int;
    var t: {{Type}};
    var v: {{V}};
    enc_k := {{ENC}}(k);
    t := $Dereference(m);
    if (!ContainsTable(t->$dynamic_fields{{S}}, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t->$dynamic_fields{{S}}, enc_k);
        assume $IsValid{{SV}}(v);
        dst := $Mutation(m->l, ExtendVec(ExtendVec(m->p, 1), enc_k), v);
        m' := m;
    }
}
{%- endif %}

{%- if impl.fun_remove != "" %}
procedure {:inline 2} {{impl.fun_remove}}{{DF_S}}(m: $Mutation ({{Type}}), k: {{K}}) returns (v: {{V}}, m': $Mutation({{Type}})) {
    var enc_k: int;
    var t: {{Type}};
    enc_k := {{ENC}}(k);
    t := $Dereference(m);
    if (!ContainsTable(t->$dynamic_fields{{S}}, enc_k)) {
        call $Abort($StdError(7/*INVALID_ARGUMENTS*/, 101/*ENOT_FOUND*/));
    } else {
        v := GetTable(t->$dynamic_fields{{S}}, enc_k);
        assume $IsValid{{SV}}(v);
        m' := $UpdateMutation(m, $Update'{{Type}}'_dynamic_fields{{S}}(t, RemoveTable(t->$dynamic_fields{{S}}, enc_k)));
    }
}
{%- endif %}

{%- if impl.fun_exists_with_type != "" %}
function {:inline} {{impl.fun_exists_with_type}}{{DF_S}}(t: ({{Type}}), k: {{K}}): bool {
    ContainsTable(t->$dynamic_fields{{S}}, {{ENC}}(k))
}
{%- endif %}

{%- if impl.fun_exists != "" %}
axiom (forall t: {{Type}}, k: {{K}} :: {({{impl.fun_exists_inner}}{{SK}}(t, k))}
   ContainsTable(t->$dynamic_fields{{S}}, {{ENC}}(k)) ==> {{impl.fun_exists_inner}}{{SK}}(t, k));
{%- endif %}

{% endmacro dynamic_field_module %}

{% macro quantifier_helpers_module(instance) %}
{%- set QP = instance.quantifier_params -%}
{%- set QA = instance.quantifier_args -%}
{%- set FN = instance.name -%}
{%- set RT = instance.result_type -%}
{%- set EAB = instance.extra_args_before -%}
{%- set EAA = instance.extra_args_after -%}

{%- if instance.qht == "find_indices" %}
function $FindIndicesQuantifierHelper_{{FN}}({{QP}}): Vec ({{RT}});
axiom (forall {{QP}} :: {$FindIndicesQuantifierHelper_{{FN}}({{QA}})}
(
    var res := $FindIndicesQuantifierHelper_{{FN}}({{QA}});
        LenVec(res) <= end - start &&
        (forall i: int, j: int :: 0 <= i && i < j && j < LenVec(res) ==> ReadVec(res, i) < ReadVec(res, j)) &&
        (forall i: int :: 0 <= i && i < LenVec(res) ==> start <= ReadVec(res, i) && ReadVec(res, i) < end) &&
        (forall i: int :: 0 <= i && i < LenVec(res) ==> {{FN}}({{EAB}}ReadVec(res, i){{EAA}})) &&
        (forall j: int :: start <= j && j < end && {{FN}}({{EAB}}ReadVec(v, j){{EAA}}) ==> ContainsVec(res, j))
    )
);
{%- endif %}

{%- if instance.qht == "filter" %}
function $FilterQuantifierHelper_{{FN}}({{QP}}): Vec ({{RT}});
axiom (forall {{QP}} :: {$FilterQuantifierHelper_{{FN}}({{QA}})}
(
    var res := $FilterQuantifierHelper_{{FN}}({{QA}});
        LenVec(res) <= end - start &&
        (forall i: int :: 0 <= i && i < LenVec(res) ==> {{FN}}({{EAB}}ReadVec(v, i){{EAA}})) &&
        (forall i: int :: 0 <= i && i < LenVec(res) ==> ContainsVec(v, ReadVec(res, i))) &&
        (forall j: int :: start <= j && j < end && {{FN}}({{EAB}}ReadVec(v, j){{EAA}}) ==> ContainsVec(res, ReadVec(v, j)))
    )
);
{%- endif %}

{%- if instance.qht == "find_index" %}
function $FindIndexQuantifierHelper_{{FN}}({{QP}}): int;
axiom (forall {{QP}} :: {$FindIndexQuantifierHelper_{{FN}}({{QA}})}
(
    var res := $FindIndexQuantifierHelper_{{FN}}({{QA}});
        if (forall i: int :: start <= i && i < end ==> !{{FN}}({{EAB}}ReadVec(v, i){{EAA}})) then res == -1
        else start <= res && res < end && {{FN}}({{EAB}}ReadVec(v, res){{EAA}}) &&
            (forall j: int :: start <= j && j < res ==> !{{FN}}({{EAB}}ReadVec(v, j){{EAA}}))
    )
);
{%- endif %}

{%- if instance.qht == "map" %}
function $MapQuantifierHelper_{{FN}}({{QP}}): Vec ({{RT}});
axiom (forall {{QP}}:: {$MapQuantifierHelper_{{FN}}({{QA}})}
(
    var res := $MapQuantifierHelper_{{FN}}({{QA}});
        LenVec(res) == end - start &&
        (forall i: int :: start <= i && i < end ==> ReadVec(res, i - start) == {{FN}}({{EAB}}ReadVec(v, i){{EAA}}))
    )
);
{%- endif %}

{%- if instance.qht == "range_map" %}
function $RangeMapQuantifierHelper_{{FN}}({{QP}}): Vec ({{RT}});
axiom (forall {{QP}}:: {$RangeMapQuantifierHelper_{{FN}}({{QA}})}
(
    var res := $RangeMapQuantifierHelper_{{FN}}({{QA}});
        LenVec(res) == (if start <= end then end - start else 0) &&
        (forall i: int :: InRangeVec(res, i) ==> ReadVec(res, i) == {{FN}}({{EAB}}(i + start){{EAA}}))
    )
);
{%- endif %}

{% endmacro quantifier_helpers_module %}

{% macro dynamic_field_key_module(impl, instance) %}
{%- set Type = impl.struct_name -%}
{%- set T = instance.name -%}
{%- set S = "'" ~ instance.suffix ~ "'" -%}
{%- set DF_S = "'" ~ instance.suffix ~ "_" ~ impl.struct_name ~ "'" -%}

{%- if impl.fun_exists != "" %}
function {{impl.fun_exists_inner}}{{DF_S}}(t: ({{Type}}), k: {{T}}): bool;

function {:inline} {{impl.fun_exists}}{{DF_S}}(t: {{Type}}, k: {{T}}): bool {
    {{impl.fun_exists_inner}}{{DF_S}}(t, k)
}
{%- endif %}

{% endmacro dynamic_field_key_module %}

{# BCS
   ====
#}

{% macro bcs_module(instance) %}
{%- set S = "'" ~ instance.suffix ~ "'" -%}
{%- set T = instance.name -%}
// Serialize is modeled as an uninterpreted function, with an additional
// axiom to say it's an injection.

function $1_bcs_serialize{{S}}(v: {{T}}): Vec int;

axiom (forall v1, v2: {{T}} :: {$1_bcs_serialize{{S}}(v1), $1_bcs_serialize{{S}}(v2)}
   $IsEqual{{S}}(v1, v2) <==> $IsEqual'vec'u8''($1_bcs_serialize{{S}}(v1), $1_bcs_serialize{{S}}(v2)));

// This says that serialize returns a non-empty vec<u8>
{% if options.serialize_bound == 0 %}
axiom (forall v: {{T}} :: {$1_bcs_serialize{{S}}(v)}
     ( var r := $1_bcs_serialize{{S}}(v); $IsValid'vec'u8''(r) && LenVec(r) > 0 ));
{% else %}
axiom (forall v: {{T}} :: {$1_bcs_serialize{{S}}(v)}
     ( var r := $1_bcs_serialize{{S}}(v); $IsValid'vec'u8''(r) && LenVec(r) > 0 &&
                            LenVec(r) <= {{options.serialize_bound}} ));
{% endif %}

function {:inline} $1_bcs_to_bytes{{S}}(v: {{T}}): Vec int {
    $1_bcs_serialize{{S}}(v)
}

{% if S == "'address'" -%}
// Serialized addresses should have the same length.
const $serialized_address_len: int;
// Serialized addresses should have the same length
axiom (forall v: int :: {$1_bcs_serialize'address'(v)}
     ( var r := $1_bcs_serialize'address'(v); LenVec(r) == $serialized_address_len));
{% endif %}
{% endmacro hash_module %}


{# Event Module
   ============
#}

{% macro event_module(instance) %}
{%- set S = "'" ~ instance.suffix ~ "'" -%}
{%- set T = instance.name -%}

// Map type specific handle to universal one.
type $1_event_EventHandle{{S}} = $1_event_EventHandle;

function {:inline} $IsEqual'$1_event_EventHandle{{S}}'(a: $1_event_EventHandle{{S}}, b: $1_event_EventHandle{{S}}): bool {
    a == b
}

function $IsValid'$1_event_EventHandle{{S}}'(h: $1_event_EventHandle{{S}}): bool {
    true
}

// Embed event `{{T}}` into universal $EventRep
function {:constructor} $ToEventRep{{S}}(e: {{T}}): $EventRep;
axiom (forall v1, v2: {{T}} :: {$ToEventRep{{S}}(v1), $ToEventRep{{S}}(v2)}
    $IsEqual{{S}}(v1, v2) <==> $ToEventRep{{S}}(v1) == $ToEventRep{{S}}(v2));

// Creates a new event handle. This ensures each time it is called that a unique new abstract event handler is
// returned.
// TODO: we should check (and abort with the right code) if no generator exists for the signer.
procedure {:inline 1} $1_event_new_event_handle{{S}}(signer: $signer) returns (res: $1_event_EventHandle{{S}}) {
    assume $1_event_EventHandles[res] == false;
    $1_event_EventHandles := $1_event_EventHandles[res := true];
}

// This boogie procedure is the model of `emit_event`. This model abstracts away the `counter` behavior, thus not
// mutating (or increasing) `counter`.
procedure {:inline 1} $1_event_emit_event{{S}}(handle_mut: $Mutation $1_event_EventHandle{{S}}, msg: {{T}})
returns (res: $Mutation $1_event_EventHandle{{S}}) {
    var handle: $1_event_EventHandle{{S}};
    handle := $Dereference(handle_mut);
    $es := $ExtendEventStore{{S}}($es, handle, msg);
    res := handle_mut;
}

procedure {:inline 1} $1_event_guid{{S}}(handle_ref: $1_event_EventHandle{{S}})
returns (res: int) {
    // TODO: temporarily mocked. The return type needs to be fixed.
    res := 0;
}

procedure {:inline 1} $1_event_counter{{S}}(handle_ref: $1_event_EventHandle{{S}})
returns (res: int) {
    // TODO: temporarily mocked.
    res := 0;
}

procedure {:inline 1} $1_event_destroy_handle{{S}}(handle: $1_event_EventHandle{{S}}) {
}

function {:inline} $ExtendEventStore{{S}}(
        es: $EventStore, handle: $1_event_EventHandle{{S}}, msg: {{T}}): $EventStore {
    (var stream := es->streams[handle];
    (var stream_new := ExtendMultiset(stream, $ToEventRep{{S}}(msg));
    $EventStore(es->counter+1, es->streams[handle := stream_new])))
}

function {:inline} $CondExtendEventStore{{S}}(
        es: $EventStore, handle: $1_event_EventHandle{{S}}, msg: {{T}}, cond: bool): $EventStore {
    if cond then
        $ExtendEventStore{{S}}(es, handle, msg)
    else
        es
}
{% endmacro event_module %}
