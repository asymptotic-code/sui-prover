/// Real number type for mathematical specifications.
/// This module provides exact real arithmetic for writing clean specs.
/// The Lean backend links these natives to Lean's Real type from Mathlib.
module prover::real;

/// Opaque real number type
public struct Real has copy, drop {}

// ============================================================================
// Constructors from unsigned integers
// ============================================================================

native public fun from_u8(n: u8): Real;
native public fun from_u16(n: u16): Real;
native public fun from_u32(n: u32): Real;
native public fun from_u64(n: u64): Real;
native public fun from_u128(n: u128): Real;
native public fun from_u256(n: u256): Real;

// ============================================================================
// Constructors from signed integers (two's complement bits)
// ============================================================================

native public fun from_i8_bits(bits: u8): Real;
native public fun from_i16_bits(bits: u16): Real;
native public fun from_i32_bits(bits: u32): Real;
native public fun from_i64_bits(bits: u64): Real;
native public fun from_i128_bits(bits: u128): Real;

// ============================================================================
// Constructor from numerator/denominator
// ============================================================================

/// Create a rational number num/den
native public fun from_fraction(num: Real, den: Real): Real;

/// Convenience: create a fraction from two u64 values
public fun fraction(num: u64, den: u64): Real {
    from_fraction(from_u64(num), from_u64(den))
}

// ============================================================================
// Basic arithmetic operations
// ============================================================================

native public fun add(a: Real, b: Real): Real;
native public fun sub(a: Real, b: Real): Real;
native public fun mul(a: Real, b: Real): Real;
native public fun div(a: Real, b: Real): Real;
native public fun neg(a: Real): Real;
native public fun abs(a: Real): Real;

// ============================================================================
// Power operations
// ============================================================================

/// Power with integer exponent (floor of exp if rational)
native public fun pow(base: Real, exp: Real): Real;

/// Convenience: power with u64 exponent
public fun pow_u64(base: Real, exp: u64): Real {
    pow(base, from_u64(exp))
}

// ============================================================================
// Rounding operations
// ============================================================================

/// Floor: largest integer <= r
native public fun floor(r: Real): Real;

/// Ceiling: smallest integer >= r
native public fun ceil(r: Real): Real;

/// Truncate: round toward zero
native public fun trunc(r: Real): Real;

/// Round to nearest integer
native public fun round(r: Real): Real;

// ============================================================================
// Floor to specific unsigned integer types
// ============================================================================

native public fun floor_u8(r: Real): u8;
native public fun floor_u16(r: Real): u16;
native public fun floor_u32(r: Real): u32;
native public fun floor_u64(r: Real): u64;
native public fun floor_u128(r: Real): u128;
native public fun floor_u256(r: Real): u256;

// ============================================================================
// Comparison operations
// ============================================================================

native public fun eq(a: Real, b: Real): bool;
native public fun ne(a: Real, b: Real): bool;
native public fun lt(a: Real, b: Real): bool;
native public fun le(a: Real, b: Real): bool;
native public fun gt(a: Real, b: Real): bool;
native public fun ge(a: Real, b: Real): bool;

// ============================================================================
// Min/Max
// ============================================================================

native public fun min(a: Real, b: Real): Real;
native public fun max(a: Real, b: Real): Real;

// ============================================================================
// Accessors
// ============================================================================

native public fun numerator(r: Real): Real;
native public fun denominator(r: Real): Real;

// ============================================================================
// Predicates
// ============================================================================

native public fun is_zero(r: Real): bool;
native public fun is_positive(r: Real): bool;
native public fun is_negative(r: Real): bool;
native public fun is_integer(r: Real): bool;

// ============================================================================
// Constants
// ============================================================================

native public fun zero(): Real;
native public fun one(): Real;

/// 2^64 - commonly needed for fixed-point conversion
public fun two_pow_64(): Real {
    from_u128(18446744073709551616) // 2^64
}

// ============================================================================
// Logarithm (symbolic only - actual computation not supported)
// ============================================================================

/// Natural logarithm (placeholder for symbolic reasoning)
native public fun ln(x: Real): Real;

/// Logarithm base b: log_b(x) = ln(x) / ln(b)
public fun log(x: Real, base: Real): Real {
    div(ln(x), ln(base))
}

// ============================================================================
// Square root (symbolic only - actual computation not supported)
// ============================================================================

/// Square root (placeholder for symbolic reasoning)
native public fun sqrt(x: Real): Real;
