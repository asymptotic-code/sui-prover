{#
Copyright (c) The Diem Core Contributors
SPDX-License-Identifier: Apache-2.0

This files contains a Tera Rust template for the prover's Boogie prelude.
(See https://tera.netlify.app/docs).

The following variables and filters are bound in the template context:

- options: contains the crate::options::BoogieOptions structure
- vec_instances: a list of crate::TypeInfo's for all vector instantiations

Below we include macros and data type theories. Notice that Tera requires to
include macros before any actual content in the template. Also note the implementation
bound to included theories is determined by the function `crate::add_prelude`, based on
options provided to the prover.
#}

{% import "native" as native %}
{% include "vector-theory" %}
{% include "multiset-theory" %}
{% include "table-theory" %}
{%- if options.custom_natives -%}
{% include "custom-natives" %}
{%- endif %}

// Prover
procedure {:inline 1} $ShlBvBv256From8(src1: bv256, src2: bv8) returns (dst: bv256) {
    call dst := $ShlBv256From8(src1, src2);
}

procedure {:inline 1} $0_prover_requires(p: bool) {
    assume p;
}

type $1_integer_Integer = int;
function {:inline} $IsValid'$1_integer_Integer'(x: int): bool {
    true
}
function {:inline} $IsEqual'$1_integer_Integer'(x: int, y: int): bool {
    x == y
}
procedure {:inline 1} $0_prover_type_inv'$1_integer_Integer'(x: int) returns (y: bool) {
    y := true;
}

{%- if include_vector_iter_range %}
function $0_vector_iter_range(start: int, end: int) returns (Vec int);
axiom (
    forall start, end: int :: {$0_vector_iter_range(start, end)}
    (
        var res := $0_vector_iter_range(start, end);
        LenVec(res) == (if start <= end then end - start else 0) &&
        (forall i: int :: InRangeVec(res, i) ==> ReadVec(res, i) == i + start)
    )
);
{%- endif %}


{%- if options.bv_int_encoding -%}

function {:inline} $1_integer_from_u8(x: int): int {
    x
}
function {:inline} $1_integer_from_u16(x: int): int {
    x
}
function {:inline} $1_integer_from_u32(x: int): int {
    x
}
function {:inline} $1_integer_from_u64(x: int): int {
    x
}
function {:inline} $1_integer_from_u128(x: int): int {
    x
}
function {:inline} $1_integer_from_u256(x: int): int {
    x
}
function {:inline} $1_integer_to_u8(x: int): int {
    x mod 256
}
function {:inline} $1_integer_to_u16(x: int): int {
    x mod 65536
}
function {:inline} $1_integer_to_u32(x: int): int {
    x mod 4294967296
}
function {:inline} $1_integer_to_u64(x: int): int {
    x mod 18446744073709551616
}
function {:inline} $1_integer_to_u128(x: int): int {
    x mod 340282366920938463463374607431768211456
}
function {:inline} $1_integer_to_u256(x: int): int {
    x mod 115792089237316195423570985008687907853269984665640564039457584007913129639936
}

{%- else %}

function {:inline} $1_integer_from_u8(x: bv8): int {
    $bv2int.8(x)
}

function {:inline} $1_integer_from_u16(x: bv16): int {
    $bv2int.16(x)
}

function {:inline} $1_integer_from_u32(x: bv32): int {
    $bv2int.32(x)
}

function {:inline} $1_integer_from_u64(x: bv64): int {
    $bv2int.64(x)
}

function {:inline} $1_integer_from_u128(x: bv128): int {
    $bv2int.128(x)
}

function {:inline} $1_integer_from_u256(x: bv256): int {
    $bv2int.256(x)
}

function {:inline} $1_integer_to_u8(x: int): bv8 {
    $int2bv.8(x)
}

function {:inline} $1_integer_to_u16(x: int): bv16 {
    $int2bv.16(x)
}

function {:inline} $1_integer_to_u32(x: int): bv32 {
    $int2bv.32(x)
}

function {:inline} $1_integer_to_u64(x: int): bv64 {
    $int2bv.64(x)
}

function {:inline} $1_integer_to_u128(x: int): bv128 {
    $int2bv.128(x)
}

function {:inline} $1_integer_to_u256(x: int): bv256 {
    $int2bv.256(x)
}

{%- endif %}

function {:inline} $1_integer_add(x: int, y: int): int {
    x + y
}

function {:inline} $1_integer_sub(x: int, y: int): int {
    x - y
}

function {:inline} $1_integer_neg(x: int): int {
    -x
}

function {:inline} $1_integer_mul(x: int, y: int): int {
    x * y
}

function {:inline} $1_integer_div(x: int, y: int): int {
    x div y
}

function {:inline} $1_integer_mod(x: int, y: int): int {
    x mod y
}

function {:inline} $1_integer_pow(x: int, y: int): int {
    $pow(x, y)
}

function {:inline} $1_integer_sqrt(x: int): int {
    $sqrt_int(x)
}

function $andInt(x: int, y: int) returns (int);
function $orInt(x: int, y: int) returns (int);
function $xorInt(x: int, y: int) returns (int);
function $notInt(x: int) returns (int);

function {:inline} $1_integer_bit_and(x: int, y: int): int {
    $andInt(x, y)
}

function {:inline} $1_integer_bit_or(x: int, y: int): int {
    $orInt(x, y)
}

function {:inline} $1_integer_bit_xor(x: int, y: int): int {
    $xorInt(x, y)
}

function {:inline} $1_integer_bit_not(x: int): int {
    $notInt(x)
}

function {:inline} $1_integer_lt(x: int, y: int): bool {
    x < y
}

function {:inline} $1_integer_gt(x: int, y: int): bool {
    x > y
}

function {:inline} $1_integer_lte(x: int, y: int): bool {
    x <= y
}

function {:inline} $1_integer_gte(x: int, y: int): bool {
    x >= y
}

function {:inline} $1_integer_div_real(x: int, y: int): real {
    x / y
}

// sui::tx_context native functions (uninterpreted)
function $2_tx_context_native_sender(): int;
function $2_tx_context_native_epoch(): int;
function $2_tx_context_native_epoch_timestamp_ms(): int;
function $2_tx_context_native_rgp(): int;
function $2_tx_context_native_gas_price(): int;

axiom $IsValid'address'($2_tx_context_native_sender());
axiom $IsValid'u64'($2_tx_context_native_epoch());
axiom $IsValid'u64'($2_tx_context_native_epoch_timestamp_ms());
axiom $IsValid'u64'($2_tx_context_native_rgp());
axiom $IsValid'u64'($2_tx_context_native_gas_price());

function $to_u8(x: int): int {
    x mod 256
}
function $to_u16(x: int): int {
    x mod 65536
}
function $to_u32(x: int): int {
    x mod 4294967296
}
function $to_u64(x: int): int {
    x mod 18446744073709551616
}
function $to_u128(x: int): int {
    x mod 340282366920938463463374607431768211456
}
function $to_u256(x: int): int {
    x mod 115792089237316195423570985008687907853269984665640564039457584007913129639936
}

function $to_i8(x: int): int {(
    var y := x mod 256;
    if y < 256 - y then
        y
    else
        y - 256
)}
function $to_i16(x: int): int {(
    var y := x mod 65536;
    if y < 65536 - y then
        y
    else
        y - 65536
)}
function $to_i32(x: int): int {(
    var y := x mod 4294967296;
    if y < 4294967296 - y then
        y
    else
        y - 4294967296
)}
function $to_i64(x: int): int {(
    var y := x mod 18446744073709551616;
    if y < 18446744073709551616 - y then
        y
    else
        y - 18446744073709551616
)}
function $to_i128(x: int): int {(
    var y := x mod 340282366920938463463374607431768211456;
    if y < 340282366920938463463374607431768211456 - y then
        y
    else
        y - 340282366920938463463374607431768211456
)}
function $to_i256(x: int): int {(
    var y := x mod 115792089237316195423570985008687907853269984665640564039457584007913129639936;
    if y < 115792089237316195423570985008687907853269984665640564039457584007913129639936 - y then
        y
    else
        y - 115792089237316195423570985008687907853269984665640564039457584007913129639936
)}

type $1_real_Real = real;
function {:inline} $IsValid'$1_real_Real'(x: real): bool {
    true
}
function {:inline} $IsEqual'$1_real_Real'(x: real, y: real): bool {
    x == y
}

function {:inline} $0_prover_type_inv'$1_real_Real'(x: real): bool {
    true
}

function {:inline} $1_real_from_integer(x: int): real {
    real(x)
}

function {:inline} $1_real_to_integer(x: real): int {
    int(x)
}

function {:inline} $1_real_add(x: real, y: real): real {
    x + y
}

function {:inline} $1_real_sub(x: real, y: real): real {
    x - y
}

function {:inline} $1_real_neg(x: real): real {
    -x
}

function {:inline} $1_real_mul(x: real, y: real): real {
    x * y
}

function {:inline} $1_real_div(x: real, y: real): real {
    x / y
}

function {:inline} $1_real_exp(x: real, y: int): real {
    // simplifications
    if y == 0 then 1.0
    else if y == 1 || y == -1 then x
    else if y == 2 then x * x
    else if y == 3 then x * x * x
    else $pow_real(x, y)
}

function {:inline} $1_real_lt(x: real, y: real): bool {
    x < y
}

function {:inline} $1_real_gt(x: real, y: real): bool {
    x > y
}

function {:inline} $1_real_lte(x: real, y: real): bool {
    x <= y
}

function {:inline} $1_real_gte(x: real, y: real): bool {
    x >= y
}

function {:inline} $1_real_sqrt(x: real): real {
    $sqrt_real(x)
}


// temporary stuff
procedure {:inline 1} $0_prover_requires_begin() {}
procedure {:inline 1} $0_prover_requires_end() {}
procedure {:inline 1} $0_prover_ensures_begin() {}
procedure {:inline 1} $0_prover_ensures_end() {}
procedure {:inline 1} $0_prover_aborts_begin() {}
procedure {:inline 1} $0_prover_aborts_end() {}
procedure {:inline 1} $0_prover_invariant_begin() {}
procedure {:inline 1} $0_prover_invariant_end() {}


// ============================================================================================
// Primitive Types

const $MAX_U8: int;
axiom $MAX_U8 == 255;
const $MAX_U16: int;
axiom $MAX_U16 == 65535;
const $MAX_U32: int;
axiom $MAX_U32 == 4294967295;
const $MAX_U64: int;
axiom $MAX_U64 == 18446744073709551615;
const $MAX_U128: int;
axiom $MAX_U128 == 340282366920938463463374607431768211455;
const $MAX_U256: int;
axiom $MAX_U256 == 115792089237316195423570985008687907853269984665640564039457584007913129639935;

const $POW_2_8: int;
axiom $POW_2_8 == 256;
const $POW_2_16: int;
axiom $POW_2_16 == 65536;
const $POW_2_32: int;
axiom $POW_2_32 == 4294967296;
const $POW_2_64: int;
axiom $POW_2_64 == 18446744073709551616;
const $POW_2_128: int;
axiom $POW_2_128 == 340282366920938463463374607431768211456;
const $POW_2_256: int;
axiom $POW_2_256 == 115792089237316195423570985008687907853269984665640564039457584007913129639936;

// Templates for bitvector operations

{%- for impl in bv_instances %}

function {:bvbuiltin "bvand"} $And'Bv{{impl.base}}'(bv{{impl.base}},bv{{impl.base}}) returns(bv{{impl.base}});
function {:bvbuiltin "bvor"} $Or'Bv{{impl.base}}'(bv{{impl.base}},bv{{impl.base}}) returns(bv{{impl.base}});
function {:bvbuiltin "bvxor"} $Xor'Bv{{impl.base}}'(bv{{impl.base}},bv{{impl.base}}) returns(bv{{impl.base}});
function {:bvbuiltin "bvadd"} $Add'Bv{{impl.base}}'(bv{{impl.base}},bv{{impl.base}}) returns(bv{{impl.base}});
function {:bvbuiltin "bvsub"} $Sub'Bv{{impl.base}}'(bv{{impl.base}},bv{{impl.base}}) returns(bv{{impl.base}});
function {:bvbuiltin "bvmul"} $Mul'Bv{{impl.base}}'(bv{{impl.base}},bv{{impl.base}}) returns(bv{{impl.base}});
function {:bvbuiltin "bvudiv"} $Div'Bv{{impl.base}}'(bv{{impl.base}},bv{{impl.base}}) returns(bv{{impl.base}});
function {:bvbuiltin "bvurem"} $Mod'Bv{{impl.base}}'(bv{{impl.base}},bv{{impl.base}}) returns(bv{{impl.base}});
function {:bvbuiltin "bvsdiv"} $SDiv'Bv{{impl.base}}'(bv{{impl.base}},bv{{impl.base}}) returns(bv{{impl.base}});
function {:bvbuiltin "bvsrem"} $SMod'Bv{{impl.base}}'(bv{{impl.base}},bv{{impl.base}}) returns(bv{{impl.base}});
function {:bvbuiltin "bvshl"} $Shl'Bv{{impl.base}}'(bv{{impl.base}},bv{{impl.base}}) returns(bv{{impl.base}});
function {:bvbuiltin "bvlshr"} $Shr'Bv{{impl.base}}'(bv{{impl.base}},bv{{impl.base}}) returns(bv{{impl.base}});
function {:bvbuiltin "bvashr"} $AShr'Bv{{impl.base}}'(bv{{impl.base}},bv{{impl.base}}) returns(bv{{impl.base}});
function {:bvbuiltin "bvult"} $Lt'Bv{{impl.base}}'(bv{{impl.base}},bv{{impl.base}}) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv{{impl.base}}'(bv{{impl.base}},bv{{impl.base}}) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv{{impl.base}}'(bv{{impl.base}},bv{{impl.base}}) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv{{impl.base}}'(bv{{impl.base}},bv{{impl.base}}) returns(bool);

procedure {:inline 1} $AddBv{{impl.base}}(src1: bv{{impl.base}}, src2: bv{{impl.base}}) returns (dst: bv{{impl.base}})
{
    if ($Lt'Bv{{impl.base}}'($Add'Bv{{impl.base}}'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv{{impl.base}}'(src1, src2);
}

procedure {:inline 1} $AddBv{{impl.base}}_unchecked(src1: bv{{impl.base}}, src2: bv{{impl.base}}) returns (dst: bv{{impl.base}})
{
    dst := $Add'Bv{{impl.base}}'(src1, src2);
}

procedure {:inline 1} $SubBv{{impl.base}}(src1: bv{{impl.base}}, src2: bv{{impl.base}}) returns (dst: bv{{impl.base}})
{
    if ($Lt'Bv{{impl.base}}'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv{{impl.base}}'(src1, src2);
}

procedure {:inline 1} $MulBv{{impl.base}}(src1: bv{{impl.base}}, src2: bv{{impl.base}}) returns (dst: bv{{impl.base}})
{
    if ($Lt'Bv{{impl.base}}'($Mul'Bv{{impl.base}}'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv{{impl.base}}'(src1, src2);
}

procedure {:inline 1} $DivBv{{impl.base}}(src1: bv{{impl.base}}, src2: bv{{impl.base}}) returns (dst: bv{{impl.base}})
{
    if (src2 == 0bv{{impl.base}}) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv{{impl.base}}'(src1, src2);
}

procedure {:inline 1} $ModBv{{impl.base}}(src1: bv{{impl.base}}, src2: bv{{impl.base}}) returns (dst: bv{{impl.base}})
{
    if (src2 == 0bv{{impl.base}}) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv{{impl.base}}'(src1, src2);
}

procedure {:inline 1} $AndBv{{impl.base}}(src1: bv{{impl.base}}, src2: bv{{impl.base}}) returns (dst: bv{{impl.base}})
{
    dst := $And'Bv{{impl.base}}'(src1,src2);
}

procedure {:inline 1} $OrBv{{impl.base}}(src1: bv{{impl.base}}, src2: bv{{impl.base}}) returns (dst: bv{{impl.base}})
{
    dst := $Or'Bv{{impl.base}}'(src1,src2);
}

procedure {:inline 1} $XorBv{{impl.base}}(src1: bv{{impl.base}}, src2: bv{{impl.base}}) returns (dst: bv{{impl.base}})
{
    dst := $Xor'Bv{{impl.base}}'(src1,src2);
}

procedure {:inline 1} $LtBv{{impl.base}}(src1: bv{{impl.base}}, src2: bv{{impl.base}}) returns (dst: bool)
{
    dst := $Lt'Bv{{impl.base}}'(src1,src2);
}

procedure {:inline 1} $LeBv{{impl.base}}(src1: bv{{impl.base}}, src2: bv{{impl.base}}) returns (dst: bool)
{
    dst := $Le'Bv{{impl.base}}'(src1,src2);
}

procedure {:inline 1} $GtBv{{impl.base}}(src1: bv{{impl.base}}, src2: bv{{impl.base}}) returns (dst: bool)
{
    dst := $Gt'Bv{{impl.base}}'(src1,src2);
}

procedure {:inline 1} $GeBv{{impl.base}}(src1: bv{{impl.base}}, src2: bv{{impl.base}}) returns (dst: bool)
{
    dst := $Ge'Bv{{impl.base}}'(src1,src2);
}

function $IsValid'bv{{impl.base}}'(v: bv{{impl.base}}): bool {
  $Ge'Bv{{impl.base}}'(v,0bv{{impl.base}}) && $Le'Bv{{impl.base}}'(v,{{impl.max}}bv{{impl.base}})
}

function {:inline} $IsEqual'bv{{impl.base}}'(x: bv{{impl.base}}, y: bv{{impl.base}}): bool {
    x == y
}

procedure {:inline 1} $0_prover_type_inv'bv{{impl.base}}'(v: bv{{impl.base}}) returns (y: bool) {
    y := true;
}

procedure {:inline 1} $int2bv{{impl.base}}(src: int) returns (dst: bv{{impl.base}})
{
    if (src > {{impl.max}}) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.{{impl.base}}(src);
}

procedure {:inline 1} $bv2int{{impl.base}}(src: bv{{impl.base}}) returns (dst: int)
{
    dst := $bv2int.{{impl.base}}(src);
}

function {:builtin "(_ int2bv {{impl.base}})"} $int2bv.{{impl.base}}(i: int) returns (bv{{impl.base}});
function {:builtin "bv2nat"} $bv2int.{{impl.base}}(i: bv{{impl.base}}) returns (int);

function $andInt'u{{impl.base}}'(x: int, y: int) returns (int) {
    $andInt(x mod $POW_2_{{impl.base}}, y mod $POW_2_{{impl.base}})
}
function $andInt'i{{impl.base}}'(x: int, y: int) returns (int) {
    $andInt($to_i{{impl.base}}(x), $to_i{{impl.base}}(y))
}
axiom (forall x, y : int :: {$andInt'u{{impl.base}}'(x, y)}
    $andInt'u{{impl.base}}'(x, y) == $andInt(x, y) mod $POW_2_{{impl.base}}
);
axiom (forall x, y : int :: {$andInt'u{{impl.base}}'(x, y)}
    0 <= $andInt'u{{impl.base}}'(x, y) && $andInt'u{{impl.base}}'(x, y) < $POW_2_{{impl.base}}
);
axiom (forall x, y : int :: {$andInt'u{{impl.base}}'(x, y)}
    $to_i{{impl.base}}($andInt'u{{impl.base}}'(x, y)) == $andInt'i{{impl.base}}'(x, y)
);
function $orInt'u{{impl.base}}'(x: int, y: int) returns (int) {
    $orInt(x mod $POW_2_{{impl.base}}, y mod $POW_2_{{impl.base}})
}
function $orInt'i{{impl.base}}'(x: int, y: int) returns (int) {
    $orInt($to_i{{impl.base}}(x), $to_i{{impl.base}}(y))
}
axiom (forall x, y : int :: {$orInt'u{{impl.base}}'(x, y)}
    $orInt'u{{impl.base}}'(x, y) == $orInt(x, y) mod $POW_2_{{impl.base}}
);
axiom (forall x, y : int :: {$orInt'u{{impl.base}}'(x, y)}
    0 <= $orInt'u{{impl.base}}'(x, y) && $orInt'u{{impl.base}}'(x, y) < $POW_2_{{impl.base}}
);
axiom (forall x, y : int :: {$orInt'u{{impl.base}}'(x, y)}
    $to_i{{impl.base}}($orInt'u{{impl.base}}'(x, y)) == $orInt'i{{impl.base}}'(x, y)
);
function $xorInt'u{{impl.base}}'(x: int, y: int) returns (int) {
    $xorInt(x mod $POW_2_{{impl.base}}, y mod $POW_2_{{impl.base}})
}
function $xorInt'i{{impl.base}}'(x: int, y: int) returns (int) {
    $xorInt($to_i{{impl.base}}(x), $to_i{{impl.base}}(y))
}
axiom (forall x, y: int :: {$xorInt'u{{impl.base}}'(x, y)}
    $xorInt'u{{impl.base}}'(x, y) == $xorInt(x, y) mod $POW_2_{{impl.base}}
);
axiom (forall x, y: int :: {$xorInt'u{{impl.base}}'(x, y)}
    0 <= $xorInt'u{{impl.base}}'(x, y) && $xorInt'u{{impl.base}}'(x, y) < $POW_2_{{impl.base}}
);
axiom (forall x, y : int :: {$xorInt'u{{impl.base}}'(x, y)}
    $to_i{{impl.base}}($xorInt'u{{impl.base}}'(x, y)) == $xorInt'i{{impl.base}}'(x, y)
);

procedure {:inline 1} $AndInt'u{{impl.base}}'(src1: int, src2: int) returns (dst: int)
{
    dst := $andInt'u{{impl.base}}'(src1, src2);
}
procedure {:inline 1} $OrInt'u{{impl.base}}'(src1: int, src2: int) returns (dst: int)
{
    dst := $orInt'u{{impl.base}}'(src1, src2);
}
procedure {:inline 1} $XorInt'u{{impl.base}}'(src1: int, src2: int) returns (dst: int)
{
    dst := $xorInt'u{{impl.base}}'(src1, src2);
}

{%- endfor %}

datatype $Range {
    $Range(lb: int, ub: int)
}

function {:inline} $IsValid'bool'(v: bool): bool {
  true
}

function $IsValid'u8'(v: int): bool {
  v >= 0 && v <= $MAX_U8
}

function $IsValid'u16'(v: int): bool {
  v >= 0 && v <= $MAX_U16
}

function $IsValid'u32'(v: int): bool {
  v >= 0 && v <= $MAX_U32
}

function $IsValid'u64'(v: int): bool {
  v >= 0 && v <= $MAX_U64
}

function $IsValid'u128'(v: int): bool {
  v >= 0 && v <= $MAX_U128
}

function $IsValid'u256'(v: int): bool {
  v >= 0 && v <= $MAX_U256
}

function {:inline} $IsValid'num'(v: int): bool {
  true
}

function $IsValid'address'(v: int): bool {
  // TODO: restrict max to representable addresses?
  v >= 0
}

function {:inline} $IsValidRange(r: $Range): bool {
   $IsValid'u64'(r->lb) &&  $IsValid'u64'(r->ub)
}

// Intentionally not inlined so it serves as a trigger in quantifiers.
function $InRange(r: $Range, i: int): bool {
   r->lb <= i && i < r->ub
}


function {:inline} $IsEqual'u8'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u16'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u32'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u64'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u128'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u256'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'num'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'address'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'bool'(x: bool, y: bool): bool {
    x == y
}

procedure {:inline 1} $0_prover_type_inv'bool'(x: bool) returns (y: bool) {
    y := true;
}

procedure {:inline 1} $0_prover_type_inv'u8'(x: int) returns (y: bool) {
    y := true;
}

procedure {:inline 1} $0_prover_type_inv'u16'(x: int) returns (y: bool) {
    y := true;
}

procedure {:inline 1} $0_prover_type_inv'u32'(x: int) returns (y: bool) {
    y := true;
}

procedure {:inline 1} $0_prover_type_inv'u64'(x: int) returns (y: bool) {
    y := true;
}

procedure {:inline 1} $0_prover_type_inv'u128'(x: int) returns (y: bool) {
    y := true;
}

procedure {:inline 1} $0_prover_type_inv'u256'(x: int) returns (y: bool) {
    y := true;
}

procedure {:inline 1} $0_prover_type_inv'num'(x: int) returns (y: bool) {
    y := true;
}

procedure {:inline 1} $0_prover_type_inv'address'(x: int) returns (y: bool) {
    y := true;
}

// ============================================================================================
// Memory

datatype $Location {
    // A global resource location within the statically known resource type's memory,
    // where `a` is an address.
    $Global(a: int),
    $SpecGlobal(s: string),
    // A local location. `i` is the unique index of the local.
    $Local(i: int),
    // The location of a reference outside of the verification scope, for example, a `&mut` parameter
    // of the function being verified. References with these locations don't need to be written back
    // when mutation ends.
    $Param(i: int),
    // The location of an uninitialized mutation. Using this to make sure that the location
    // will not be equal to any valid mutation locations, i.e., $Local, $Global, or $Param.
    $Uninitialized()
}

// A mutable reference which also carries its current value. Since mutable references
// are single threaded in Move, we can keep them together and treat them as a value
// during mutation until the point they are stored back to their original location.
datatype $Mutation<T> {
    $Mutation(l: $Location, p: Vec int, v: T)
}

// Representation of memory for a given type.
datatype $Memory<T> {
    $Memory(domain: [int]bool, contents: [int]T)
}

function {:builtin "MapConst"} $ConstMemoryDomain(v: bool): [int]bool;
function {:builtin "MapConst"} $ConstMemoryContent<T>(v: T): [int]T;
axiom $ConstMemoryDomain(false) == (lambda i: int :: false);
axiom $ConstMemoryDomain(true) == (lambda i: int :: true);


// Dereferences a mutation.
function {:inline} $Dereference<T>(ref: $Mutation T): T {
    ref->v
}

// Update the value of a mutation.
function {:inline} $UpdateMutation<T>(m: $Mutation T, v: T): $Mutation T {
    $Mutation(m->l, m->p, v)
}

function {:inline} $ChildMutation<T1, T2>(m: $Mutation T1, offset: int, v: T2): $Mutation T2 {
    $Mutation(m->l, ExtendVec(m->p, offset), v)
}

// Return true if two mutations share the location and path
function {:inline} $IsSameMutation<T1, T2>(parent: $Mutation T1, child: $Mutation T2 ): bool {
    parent->l == child->l && parent->p == child->p
}

// Return true if the mutation is a parent of a child which was derived with the given edge offset. This
// is used to implement write-back choices.
function {:inline} $IsParentMutation<T1, T2>(parent: $Mutation T1, edge: int, child: $Mutation T2 ): bool {
    parent->l == child->l &&
    (var pp := parent->p;
    (var cp := child->p;
    (var pl := LenVec(pp);
    (var cl := LenVec(cp);
     cl == pl + 1 &&
     (forall i: int:: i >= 0 && i < pl ==> ReadVec(pp, i) ==  ReadVec(cp, i)) &&
     $EdgeMatches(ReadVec(cp, pl), edge)
    ))))
}

// Return true if the mutation is a parent of a child, for hyper edge.
function {:inline} $IsParentMutationHyper<T1, T2>(parent: $Mutation T1, hyper_edge: Vec int, child: $Mutation T2 ): bool {
    parent->l == child->l &&
    (var pp := parent->p;
    (var cp := child->p;
    (var pl := LenVec(pp);
    (var cl := LenVec(cp);
    (var el := LenVec(hyper_edge);
     cl == pl + el &&
     (forall i: int:: i >= 0 && i < pl ==> ReadVec(pp, i) == ReadVec(cp, i)) &&
     (forall i: int:: i >= 0 && i < el ==> $EdgeMatches(ReadVec(cp, pl + i), ReadVec(hyper_edge, i)))
    )))))
}

function {:inline} $EdgeMatches(edge: int, edge_pattern: int): bool {
    edge_pattern == -1 // wildcard
    || edge_pattern == edge
}



function {:inline} $SameLocation<T1, T2>(m1: $Mutation T1, m2: $Mutation T2): bool {
    m1->l == m2->l
}

function {:inline} $HasGlobalLocation<T>(m: $Mutation T): bool {
    (m->l) is $Global
}

function {:inline} $HasLocalLocation<T>(m: $Mutation T, idx: int): bool {
    m->l == $Local(idx)
}

function {:inline} $GlobalLocationAddress<T>(m: $Mutation T): int {
    (m->l)->a
}



// Tests whether resource exists.
function {:inline} $ResourceExists<T>(m: $Memory T, addr: int): bool {
    m->domain[addr]
}

// Obtains Value of given resource.
function {:inline} $ResourceValue<T>(m: $Memory T, addr: int): T {
    m->contents[addr]
}

// Update resource.
function {:inline} $ResourceUpdate<T>(m: $Memory T, a: int, v: T): $Memory T {
    $Memory(m->domain[a := true], m->contents[a := v])
}

// Remove resource.
function {:inline} $ResourceRemove<T>(m: $Memory T, a: int): $Memory T {
    $Memory(m->domain[a := false], m->contents)
}

// Copies resource from memory s to m.
function {:inline} $ResourceCopy<T>(m: $Memory T, s: $Memory T, a: int): $Memory T {
    $Memory(m->domain[a := s->domain[a]],
            m->contents[a := s->contents[a]])
}



// ============================================================================================
// Abort Handling

var $abort_flag: bool;
var $abort_code: int;

function {:inline} $process_abort_code(code: int): int {
    code
}

const $EXEC_FAILURE_CODE: int;
axiom $EXEC_FAILURE_CODE == -1;

// TODO(wrwg): currently we map aborts of native functions like those for vectors also to
//   execution failure. This may need to be aligned with what the runtime actually does.

procedure {:inline 1} $ExecFailureAbort() {
    $abort_flag := true;
    $abort_code := $EXEC_FAILURE_CODE;
}

procedure {:inline 1} $Abort(code: int) {
    $abort_flag := true;
    $abort_code := code;
}

function {:inline} $StdError(cat: int, reason: int): int {
    reason * 256 + cat
}

procedure {:inline 1} $InitVerification() {
    // Set abort_flag to false, and havoc abort_code
    $abort_flag := false;
    havoc $abort_code;
    // Initialize event store
    call $InitEventStore();
}

// ============================================================================================
// Instructions


procedure {:inline 1} $CastU8(src: int) returns (dst: int)
{
    if (src > $MAX_U8) {
        call $ExecFailureAbort();
    }
    dst := src;
}

procedure {:inline 1} $CastU16(src: int) returns (dst: int)
{
    if (src > $MAX_U16) {
        call $ExecFailureAbort();
    }
    dst := src;
}

procedure {:inline 1} $CastU32(src: int) returns (dst: int)
{
    if (src > $MAX_U32) {
        call $ExecFailureAbort();
    }
    dst := src;
}

procedure {:inline 1} $CastU64(src: int) returns (dst: int)
{
    if (src > $MAX_U64) {
        call $ExecFailureAbort();
    }
    dst := src;
}

procedure {:inline 1} $CastU128(src: int) returns (dst: int)
{
    if (src > $MAX_U128) {
        call $ExecFailureAbort();
    }
    dst := src;
}

procedure {:inline 1} $CastU256(src: int) returns (dst: int)
{
    if (src > $MAX_U256) {
        call $ExecFailureAbort();
    }
    dst := src;
}

procedure {:inline 1} $AddU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U8) {
        call $ExecFailureAbort();
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU16(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U16) {
        call $ExecFailureAbort();
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU16_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU32(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U32) {
        call $ExecFailureAbort();
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU32_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU64(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U64) {
        call $ExecFailureAbort();
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU64_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU128(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U128) {
        call $ExecFailureAbort();
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU128_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU256(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U256) {
        call $ExecFailureAbort();
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU256_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $Sub(src1: int, src2: int) returns (dst: int)
{
    if (src1 < src2) {
        call $ExecFailureAbort();
    }
    dst := src1 - src2;
}

// uninterpreted function to return an undefined value.
function $undefined_int(): int;

// Recursive exponentiation function
// Undefined unless e >=0.  $pow(0,0) is also undefined.
function $pow(n: int, e: int): int {
    if n != 0 && e == 0 then 1
    else if e > 0 then n * $pow(n, e - 1)
    else $undefined_int()
}

function $pow_real(n: real, e: int): real {
    if n == 0.0 then 0.0
    else (
        if e == 0 then 1.0
        else if e > 0 then n * $pow_real(n, e - 1)
        else 1.0 / $pow_real(n, -e)
    )
}

function $shl(src1: int, p: int): int {
    src1 * $pow(2, p)
}

function $shlU8(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 256
}

function $shlU16(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 65536
}

function $shlU32(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 4294967296
}

function $shlU64(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 18446744073709551616
}

function $shlU128(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 340282366920938463463374607431768211456
}

function $shlU256(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 115792089237316195423570985008687907853269984665640564039457584007913129639936
}

function $shr(src1: int, p: int): int {
    src1 div $pow(2, p)
}

// Integer 2 root function (floor)
// $sqrt_int(x) returns the largest integer r such that r^2 <= x
// i.e., floor(x^(1/2))
// Undefined for x < 0
function $sqrt_int(x: int): int;

// Core axioms for $sqrt_int (these uniquely define the function)
axiom (forall x: int :: x >= 0 ==> $sqrt_int(x) >= 0);
axiom (forall x: int :: x >= 0 ==> $sqrt_int(x) * $sqrt_int(x) <= x);
axiom (forall x: int :: x >= 0 ==> ($sqrt_int(x) + 1) * ($sqrt_int(x) + 1) > x);

// Edge case axioms for $sqrt_int (derived, but help SMT solver)
axiom $sqrt_int(0) == 0;
axiom $sqrt_int(1) == 1;

// Real 2 root function
// $sqrt_real(x, 2) returns x^(1/2) - the 2-th root of x
// Undefined for x < 0
function $sqrt_real(x: real): real;

// Core axioms for $sqrt_real
axiom (forall x: real :: x >= 0.0 ==> $sqrt_real(x) >= 0.0);
axiom (forall x: real :: x >= 0.0 ==> $sqrt_real(x) * $sqrt_real(x) == x);

// Edge case axioms for $sqrt_real
axiom $sqrt_real(0.0) == 0.0;
axiom $sqrt_real(1.0) == 1.0;

// We need to know the size of the destination in order to drop bits
// that have been shifted left more than that, so we have $ShlU8/16/32/64/128/256
procedure {:inline 1} $ShlU8(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU8(src1, src2);
}

// Template for cast and shift operations of bitvector types

{%- for impl in bv_instances %}
{%- for instance in sh_instances %}
{%- set base_diff = impl.base - instance %}

procedure {:inline 1} $CastBv{{instance}}to{{impl.base}}(src: bv{{instance}}) returns (dst: bv{{impl.base}})
{
    {%- if base_diff < 0 %}
    if ($Gt'Bv{{instance}}'(src, {{impl.max}}bv{{instance}})) {
            call $ExecFailureAbort();
            return;
    }
    {%- endif %}
    {%- if base_diff < 0 %}
    dst := src[{{impl.base}}:0];
    {%- elif base_diff == 0 %}
    dst := src;
    {%- else %}
    dst := 0bv{{base_diff}} ++ src;
    {%- endif %}
}


function $shlBv{{impl.base}}From{{instance}}(src1: bv{{impl.base}}, src2: bv{{instance}}) returns (bv{{impl.base}})
{
    {%- if base_diff > 0 %}
    $Shl'Bv{{impl.base}}'(src1, 0bv{{base_diff}} ++ src2)
    {%- elif base_diff == 0 %}
    $Shl'Bv{{impl.base}}'(src1, src2)
    {%- else %}
    $Shl'Bv{{impl.base}}'(src1, src2[{{impl.base}}:0])
    {%- endif %}
}

procedure {:inline 1} $ShlBv{{impl.base}}From{{instance}}(src1: bv{{impl.base}}, src2: bv{{instance}}) returns (dst: bv{{impl.base}})
{
    if ($Ge'Bv{{instance}}'(src2, {{impl.base}}bv{{instance}})) {
        call $ExecFailureAbort();
        return;
    }
    {%- if base_diff > 0 %}
    dst := $Shl'Bv{{impl.base}}'(src1, 0bv{{base_diff}} ++ src2);
    {%- elif base_diff == 0 %}
    dst := $Shl'Bv{{impl.base}}'(src1, src2);
    {%- else %}
    dst := $Shl'Bv{{impl.base}}'(src1, src2[{{impl.base}}:0]);
    {%- endif %}
}

function $shrBv{{impl.base}}From{{instance}}(src1: bv{{impl.base}}, src2: bv{{instance}}) returns (bv{{impl.base}})
{
    {%- if base_diff > 0 %}
    $Shr'Bv{{impl.base}}'(src1, 0bv{{base_diff}} ++ src2)
    {%- elif base_diff == 0 %}
    $Shr'Bv{{impl.base}}'(src1, src2)
    {%- else %}
    $Shr'Bv{{impl.base}}'(src1, src2[{{impl.base}}:0])
    {%- endif %}
}

procedure {:inline 1} $ShrBv{{impl.base}}From{{instance}}(src1: bv{{impl.base}}, src2: bv{{instance}}) returns (dst: bv{{impl.base}})
{
    if ($Ge'Bv{{instance}}'(src2, {{impl.base}}bv{{instance}})) {
        call $ExecFailureAbort();
        return;
    }
    {%- if base_diff > 0 %}
    dst := $Shr'Bv{{impl.base}}'(src1, 0bv{{base_diff}} ++ src2);
    {%- elif base_diff == 0 %}
    dst := $Shr'Bv{{impl.base}}'(src1, src2);
    {%- else %}
    dst := $Shr'Bv{{impl.base}}'(src1, src2[{{impl.base}}:0]);
    {%- endif %}
}

{%- endfor %}
{%- endfor %}

procedure {:inline 1} $ShlU16(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU16(src1, src2);
}

procedure {:inline 1} $ShlU32(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU32(src1, src2);
}

procedure {:inline 1} $ShlU64(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 64) {
       call $ExecFailureAbort();
       return;
    }
    dst := $shlU64(src1, src2);
}

procedure {:inline 1} $ShlU128(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU128(src1, src2);
}

procedure {:inline 1} $ShlU256(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shlU256(src1, src2);
}

procedure {:inline 1} $Shr(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU8(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU16(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU32(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU64(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 64) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU128(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU256(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shr(src1, src2);
}

procedure {:inline 1} $MulU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U8) {
        call $ExecFailureAbort();
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU16(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U16) {
        call $ExecFailureAbort();
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU32(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U32) {
        call $ExecFailureAbort();
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU64(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U64) {
        call $ExecFailureAbort();
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU128(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U128) {
        call $ExecFailureAbort();
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU256(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U256) {
        call $ExecFailureAbort();
    }
    dst := src1 * src2;
}

procedure {:inline 1} $Div(src1: int, src2: int) returns (dst: int)
{
    if (src2 == 0) {
        call $ExecFailureAbort();
    }
    dst := src1 div src2;
}

procedure {:inline 1} $Mod(src1: int, src2: int) returns (dst: int)
{
    if (src2 == 0) {
        call $ExecFailureAbort();
    }
    dst := src1 mod src2;
}

procedure {:inline 1} $ArithBinaryUnimplemented(src1: int, src2: int) returns (dst: int);

procedure {:inline 1} $Lt(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 < src2;
}

procedure {:inline 1} $Gt(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 > src2;
}

procedure {:inline 1} $Le(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 <= src2;
}

procedure {:inline 1} $Ge(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 >= src2;
}

procedure {:inline 1} $And(src1: bool, src2: bool) returns (dst: bool)
{
    dst := src1 && src2;
}

procedure {:inline 1} $Or(src1: bool, src2: bool) returns (dst: bool)
{
    dst := src1 || src2;
}

procedure {:inline 1} $Not(src: bool) returns (dst: bool)
{
    dst := !src;
}

// Pack and Unpack are auto-generated for each type T

// ==================================================================================
// Native Option

{%- for instance in option_instances %}

// ----------------------------------------------------------------------------------
// Native Option implementation for element type `{{instance.suffix}}`

{{ native::option_module(instance=instance) -}}
{%- endfor %}


// ==================================================================================
// Native Vector

function {:inline} $SliceVecByRange<T>(v: Vec T, r: $Range): Vec T {
    SliceVec(v, r->lb, r->ub)
}

{%- for instance in vec_instances %}

// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `{{instance.suffix}}`

{{ native::vector_module(instance=instance) -}}
{%- endfor %}

// ==================================================================================
// Native VecSet

{%- for instance in vec_set_instances %}

// ----------------------------------------------------------------------------------
// Native VecSet implementation for element type `{{instance.suffix}}`

{{ native::vec_set_module(instance=instance) -}}
{%- endfor %}

// ==================================================================================
// Native TableVec

{%- for instance in table_vec_instances %}

// ----------------------------------------------------------------------------------
// Native TableVec implementation for element type `{{instance.suffix}}`

{{ native::table_vec_module(instance=instance) -}}
{%- endfor %}

// ==================================================================================
// Native VecMap

{%- for instance in vec_map_instances %}

// ----------------------------------------------------------------------------------
// Native VecMap implementation for key type `{{instance.0.suffix}}` and value type `{{instance.1.suffix}}`

{{ native::vec_map_module(key_instance=instance.0, value_instance=instance.1) -}}
{%- endfor %}

// ==================================================================================
// Native Table

{%- for instance in table_key_instances %}

// ----------------------------------------------------------------------------------
// Native Table key encoding for type `{{instance.suffix}}`

{{ native::table_key_encoding(instance=instance) -}}
{%- endfor %}

{%- for instance in table_value_instances %}

// ----------------------------------------------------------------------------------
// Native TableArray IsValid and IsEqual implementation for type `{{instance.suffix}}`

{{ native::table_is_valid_is_equal(instance=instance) -}}
{%- endfor %}

{%- for impl in table_instances %}
{%- for instance in impl.insts %}

// ----------------------------------------------------------------------------------
// Native Table implementation for type `({{instance.0.suffix}},{{instance.1.suffix}})`

{{ native::table_module(impl=impl, instance=instance) -}}
{%- endfor %}
{%- endfor %}

{%- for impl in dynamic_field_instances %}
{%- for instance in impl.insts %}

// ----------------------------------------------------------------------------------
// Native dynamic fields implementation for type `({{instance.0.suffix}},{{instance.1.suffix}})`

{{ native::dynamic_field_module(impl=impl, instance=instance) -}}
{%- endfor %}

{%- for instance in impl.key_insts %}

// ----------------------------------------------------------------------------------
// Native dynamic fields implementation for key type `({{instance.suffix}})`

{{ native::dynamic_field_key_module(impl=impl, instance=instance) -}}
{%- endfor %}
{%- endfor %}

{%- for instance in quantifier_helpers_instances %}
// ----------------------------------------------------------------------------------
// Native Quantifier helper `{{instance.qht}}` implementation for func `{{instance.name}}`
{{ native::quantifier_helpers_module(instance=instance) -}}
{%- endfor %}

// ==================================================================================
// Native Hash

// Hash is modeled as an otherwise uninterpreted injection.
// In truth, it is not an injection since the domain has greater cardinality
// (arbitrary length vectors) than the co-domain (vectors of length 32).  But it is
// common to assume in code there are no hash collisions in practice.  Fortunately,
// Boogie is not smart enough to recognized that there is an inconsistency.
// FIXME: If we were using a reliable extensional theory of arrays, and if we could use ==
// instead of $IsEqual, we might be able to avoid so many quantified formulas by
// using a sha2_inverse function in the ensures conditions of Hash_sha2_256 to
// assert that sha2/3 are injections without using global quantified axioms.


function $1_hash_sha2(val: Vec int): Vec int;

// This says that Hash_sha2 is bijective.
axiom (forall v1,v2: Vec int :: {$1_hash_sha2(v1), $1_hash_sha2(v2)}
       $IsEqual'vec'u8''(v1, v2) <==> $IsEqual'vec'u8''($1_hash_sha2(v1), $1_hash_sha2(v2)));

procedure $1_hash_sha2_256(val: Vec int) returns (res: Vec int);
ensures res == $1_hash_sha2(val);     // returns Hash_sha2 Value
ensures $IsValid'vec'u8''(res);    // result is a legal vector of U8s.
ensures LenVec(res) == 32;               // result is 32 bytes.

// Spec version of Move native function.
function {:inline} $1_hash_$sha2_256(val: Vec int): Vec int {
    $1_hash_sha2(val)
}

// similarly for Hash_sha3
function $1_hash_sha3(val: Vec int): Vec int;

axiom (forall v1,v2: Vec int :: {$1_hash_sha3(v1), $1_hash_sha3(v2)}
       $IsEqual'vec'u8''(v1, v2) <==> $IsEqual'vec'u8''($1_hash_sha3(v1), $1_hash_sha3(v2)));

procedure $1_hash_sha3_256(val: Vec int) returns (res: Vec int);
ensures res == $1_hash_sha3(val);     // returns Hash_sha3 Value
ensures $IsValid'vec'u8''(res);    // result is a legal vector of U8s.
ensures LenVec(res) == 32;               // result is 32 bytes.

// Spec version of Move native function.
function {:inline} $1_hash_$sha3_256(val: Vec int): Vec int {
    $1_hash_sha3(val)
}

// ==================================================================================
// Native diem_account

procedure {:inline 1} $1_DiemAccount_create_signer(
  addr: int
) returns (signer: $signer) {
    // A signer is currently identical to an address.
    signer := $signer(addr);
}

procedure {:inline 1} $1_DiemAccount_destroy_signer(
  signer: $signer
) {
  return;
}

// ==================================================================================
// Native account

procedure {:inline 1} $1_Account_create_signer(
  addr: int
) returns (signer: $signer) {
    // A signer is currently identical to an address.
    signer := $signer(addr);
}

// ==================================================================================
// Native Signer

datatype $signer {
    $signer($addr: int)
}
function {:inline} $IsValid'signer'(s: $signer): bool {
    $IsValid'address'(s->$addr)
}
function {:inline} $IsEqual'signer'(s1: $signer, s2: $signer): bool {
    s1 == s2
}

procedure {:inline 1} $1_signer_borrow_address(signer: $signer) returns (res: int) {
    res := signer->$addr;
}

function {:inline} $1_signer_$borrow_address(signer: $signer): int
{
    signer->$addr
}

function $1_signer_is_txn_signer(s: $signer): bool;

function $1_signer_is_txn_signer_addr(a: int): bool;


// ==================================================================================
// Native signature

// Signature related functionality is handled via uninterpreted functions. This is sound
// currently because we verify every code path based on signature verification with
// an arbitrary interpretation.

function $1_Signature_$ed25519_validate_pubkey(public_key: Vec int): bool;
function $1_Signature_$ed25519_verify(signature: Vec int, public_key: Vec int, message: Vec int): bool;

// Needed because we do not have extensional equality:
axiom (forall k1, k2: Vec int ::
    {$1_Signature_$ed25519_validate_pubkey(k1), $1_Signature_$ed25519_validate_pubkey(k2)}
    $IsEqual'vec'u8''(k1, k2) ==> $1_Signature_$ed25519_validate_pubkey(k1) == $1_Signature_$ed25519_validate_pubkey(k2));
axiom (forall s1, s2, k1, k2, m1, m2: Vec int ::
    {$1_Signature_$ed25519_verify(s1, k1, m1), $1_Signature_$ed25519_verify(s2, k2, m2)}
    $IsEqual'vec'u8''(s1, s2) && $IsEqual'vec'u8''(k1, k2) && $IsEqual'vec'u8''(m1, m2)
    ==> $1_Signature_$ed25519_verify(s1, k1, m1) == $1_Signature_$ed25519_verify(s2, k2, m2));


procedure {:inline 1} $1_Signature_ed25519_validate_pubkey(public_key: Vec int) returns (res: bool) {
    res := $1_Signature_$ed25519_validate_pubkey(public_key);
}

procedure {:inline 1} $1_Signature_ed25519_verify(
        signature: Vec int, public_key: Vec int, message: Vec int) returns (res: bool) {
    res := $1_Signature_$ed25519_verify(signature, public_key, message);
}


// ==================================================================================
// Native bcs::serialize

{%- for instance in bcs_instances %}

// ----------------------------------------------------------------------------------
// Native BCS implementation for element type `{{instance.suffix}}`

{{ native::bcs_module(instance=instance) -}}
{%- endfor %}


// ==================================================================================
// Native Event module

{% set emit_generic_event = true %}
{%- for instance in event_instances %}
{%- if emit_generic_event %}
{% set_global emit_generic_event = false %}

// Generic code for dealing with mutations (havoc) still requires type and memory declarations.
type $1_event_EventHandleGenerator;
var $1_event_EventHandleGenerator_$memory: $Memory $1_event_EventHandleGenerator;

// Abstract type of event handles.
type $1_event_EventHandle;

// Global state to implement uniqueness of event handles.
var $1_event_EventHandles: [$1_event_EventHandle]bool;

// Universal representation of an an event. For each concrete event type, we generate a constructor.
type $EventRep;

// Representation of EventStore that consists of event streams.
datatype $EventStore {
    $EventStore(counter: int, streams: [$1_event_EventHandle]Multiset $EventRep)
}

// Global state holding EventStore.
var $es: $EventStore;

procedure {:inline 1} $InitEventStore() {
    assume $EventStore__is_empty($es);
}

function {:inline} $EventStore__is_empty(es: $EventStore): bool {
    (es->counter == 0) &&
    (forall handle: $1_event_EventHandle ::
        (var stream := es->streams[handle];
        IsEmptyMultiset(stream)))
}

// This function returns (es1 - es2). This function assumes that es2 is a subset of es1.
function {:inline} $EventStore__subtract(es1: $EventStore, es2: $EventStore): $EventStore {
    $EventStore(es1->counter-es2->counter,
        (lambda handle: $1_event_EventHandle ::
        SubtractMultiset(
            es1->streams[handle],
            es2->streams[handle])))
}

function {:inline} $EventStore__is_subset(es1: $EventStore, es2: $EventStore): bool {
    (es1->counter <= es2->counter) &&
    (forall handle: $1_event_EventHandle ::
        IsSubsetMultiset(
            es1->streams[handle],
            es2->streams[handle]
        )
    )
}

procedure {:inline 1} $EventStore__diverge(es: $EventStore) returns (es': $EventStore) {
    assume $EventStore__is_subset(es, es');
}

const $EmptyEventStore: $EventStore;
axiom $EventStore__is_empty($EmptyEventStore);

{%- endif %}

// ----------------------------------------------------------------------------------
// Native Event implementation for element type `{{instance.suffix}}`

{{ native::event_module(instance=instance) }}

{%- endfor %}

{%- if emit_generic_event %}
{# Need to at least define this procedure #}
procedure {:inline 1} $InitEventStore() {
}
{%- endif %}

// ============================================================================================
// Type Reflection on Type Parameters

datatype $TypeParamInfo {
    $TypeParamBool(),
    $TypeParamU8(),
    $TypeParamU16(),
    $TypeParamU32(),
    $TypeParamU64(),
    $TypeParamU128(),
    $TypeParamU256(),
    $TypeParamAddress(),
    $TypeParamSigner(),
    $TypeParamVector(e: $TypeParamInfo),
    $TypeParamStruct(a: int, m: Vec int, s: Vec int)
}
