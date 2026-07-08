use super::*;

#[test]
fn test_more_special_values() {
    let zero = Fraction::new(0, 1);
    let inf = Fraction::new(1, 0);
    let neg_inf = Fraction::new(-1, 0);
    let nan = Fraction::new(0, 0);

    // Division by zero
    assert_eq!(Fraction::new(1, 1) / zero, inf);
    assert_eq!(Fraction::new(-1, 1) / zero, neg_inf);

    // NaN arithmetic
    assert!((nan + inf).is_nan());
    assert!((nan - inf).is_nan());
    assert!((nan * inf).is_nan());
    assert!((nan / inf).is_nan());
    assert!((inf + nan).is_nan());
    assert!((inf - nan).is_nan());
    assert!((inf * nan).is_nan());
    assert!((inf / nan).is_nan());
}

#[test]
fn test_extra_const_gcd() {
    assert_eq!(const_gcd(0, 0), 0);
    assert_eq!(const_gcd(1, 0), 1);
    assert_eq!(const_gcd(0, 1), 1);
    assert_eq!(const_gcd(-1, 0), 1);
    assert_eq!(const_gcd(0, -1), 1);
    assert_eq!(const_gcd(10, 20), 10);
    assert_eq!(const_gcd(-10, 20), 10);
    assert_eq!(const_gcd(10, -20), 10);
    assert_eq!(const_gcd(-10, -20), 10);
}

#[test]
fn test_extra_cross() {
    let f1 = Fraction::new(1, 2);
    let f2 = Fraction::new(3, 4);
    assert_eq!(f1.cross(&f2), -2);

    let f3 = Fraction::new(0, 1);
    assert_eq!(f1.cross(&f3), 1);

    let f4 = Fraction::new(-1, 2);
    assert_eq!(f1.cross(&f4), 4);
}

#[test]
fn test_extra_reciprocal() {
    let mut f1 = Fraction::new(2, 1);
    f1.reciprocal();
    assert_eq!(f1, Fraction::new(1, 2));

    let mut f2 = Fraction::new(1, 1);
    f2.reciprocal();
    assert_eq!(f2, Fraction::new(1, 1));

    let mut f3 = Fraction::new(10, 5);
    f3.reciprocal();
    assert_eq!(f3, Fraction::new(1, 2));
}

#[test]
fn test_extra_special_values() {
    let inf = Fraction::new(1, 0);
    let neg_inf = Fraction::new(-1, 0);

    assert!((inf + neg_inf).is_nan());
    assert!((neg_inf + inf).is_nan());

    assert!((inf / inf).is_nan());
    assert!((inf / neg_inf).is_nan());
    assert!((neg_inf / inf).is_nan());
    assert!((neg_inf / neg_inf).is_nan());

    assert!((inf * Fraction::new(0, 1)).is_nan());
    assert!((neg_inf * Fraction::new(0, 1)).is_nan());
}

#[test]
fn test_from_i32_to_i64() {
    let f_i32 = 3;
    let f_i64 = Fraction::<i64>::from(f_i32);
    assert_eq!(f_i64, Fraction::new(3i64, 1i64));
}

#[cfg(feature = "num-bigint")]
#[test]
fn test_bigint_raw_construction() {
    use num_bigint::BigInt;

    let num = BigInt::from(1);
    let den = BigInt::from(2);
    let f = Fraction::new_raw(num, den);

    assert_eq!(*f.numer(), BigInt::from(1));
    assert_eq!(*f.denom(), BigInt::from(2));
    assert!(!f.is_zero());

    let inf = Fraction::new_raw(BigInt::from(1), BigInt::from(0));
    assert!(inf.is_infinite());
}

#[cfg(feature = "num-bigint")]
#[test]
fn test_bigint_zero_one() {
    use num_bigint::BigInt;

    let zero = Fraction::<BigInt>::zero();
    assert_eq!(*zero.numer(), BigInt::from(0));
    assert_eq!(*zero.denom(), BigInt::from(1));
    assert!(zero.is_zero());

    let one = Fraction::<BigInt>::one();
    assert_eq!(*one.numer(), BigInt::from(1));
    assert_eq!(*one.denom(), BigInt::from(1));
}

#[cfg(feature = "num-bigint")]
#[test]
fn test_bigint_special_values() {
    use num_bigint::BigInt;

    let inf = Fraction::new_raw(BigInt::from(1), BigInt::from(0));
    let neg_inf = Fraction::new_raw(BigInt::from(-1), BigInt::from(0));
    let nan = Fraction::new_raw(BigInt::from(0), BigInt::from(0));

    assert!(inf.is_infinite());
    assert!(neg_inf.is_infinite());
    assert!(nan.is_nan());
}

// ============================================================================
// Tests for improving code coverage - based on cargo llvm-cov report
// ============================================================================

#[test]
fn test_div_assign_zero_divided_by_zero() {
    // Line 1178: self.is_zero() && other.is_zero() -> NaN
    let zero = Fraction::new(0, 1);
    let mut f = Fraction::new(0, 1);
    f /= zero;
    assert!(f.is_nan());
}

#[test]
fn test_add_assign_same_denominator() {
    // Line 1335: self.denom == other.denom -> optimize path
    let mut f1 = Fraction::new(1, 4);
    let f2 = Fraction::new(2, 4);
    f1 += f2;
    assert_eq!(f1, Fraction::new(3, 4));

    // Also test with denominator = 1 (optimized path further)
    let mut f3 = Fraction::new(5, 1);
    f3 += Fraction::new(3, 1);
    assert_eq!(f3, Fraction::new(8, 1));
}

#[test]
fn test_add_assign_self_is_infinite() {
    // Line 1327: self.is_infinite() -> return (keep self as inf)
    let mut inf = Fraction::new(1, 0);
    inf += Fraction::new(1, 1);
    assert!(inf.is_infinite());

    let mut neg_inf = Fraction::new(-1, 0);
    neg_inf += Fraction::new(1, 1);
    assert!(neg_inf.is_infinite());
    // Check negative via numerator
    assert!(*neg_inf.numer() < 0);
}

#[test]
fn test_add_assign_other_is_infinite() {
    // Line 1330: other.is_infinite() -> copy other to self
    let mut f = Fraction::new(1, 2);
    f += Fraction::new(1, 0);
    assert!(f.is_infinite());

    let mut f2 = Fraction::new(1, 2);
    f2 += Fraction::new(-1, 0);
    assert!(f2.is_infinite());
    assert!(*f2.numer() < 0);
}

#[test]
fn test_add_assign_both_infinite_opposite_sign() {
    // Line 1321-1325: both infinite with opposite sign -> NaN
    let mut inf = Fraction::new(1, 0);
    inf += Fraction::new(-1, 0);
    assert!(inf.is_nan());

    let mut neg_inf = Fraction::new(-1, 0);
    neg_inf += Fraction::new(1, 0);
    assert!(neg_inf.is_nan());
}

#[test]
fn test_sub_assign_both_infinite() {
    // Line 1248: self.is_infinite() && other.is_infinite() -> NaN
    let mut inf = Fraction::new(1, 0);
    inf -= Fraction::new(1, 0);
    assert!(inf.is_nan());
}

#[test]
fn test_sub_assign_self_is_infinite() {
    // Line 1252: self.is_infinite() -> return (keep self as inf)
    let mut inf = Fraction::new(1, 0);
    inf -= Fraction::new(1, 1);
    assert!(inf.is_infinite());
}

#[test]
fn test_sub_assign_other_is_infinite() {
    // Line 1255: other.is_infinite() -> negate other
    let mut f = Fraction::new(1, 2);
    f -= Fraction::new(1, 0);
    assert!(f.is_infinite());
    // Check negative via numerator
    assert!(*f.numer() < 0);

    let mut f2 = Fraction::new(1, 2);
    f2 -= Fraction::new(-1, 0);
    assert!(f2.is_infinite());
}

#[test]
fn test_sub_assign_same_denominator() {
    // Line 1260: optimize path when same denominator
    let mut f1 = Fraction::new(3, 4);
    let f2 = Fraction::new(1, 4);
    f1 -= f2;
    assert_eq!(f1, Fraction::new(1, 2));
}

#[test]
fn test_div_assign_inf_divided_by_inf() {
    // Line 1174: both infinite -> NaN
    let mut f1 = Fraction::new(1, 0);
    let f2 = Fraction::new(1, 0);
    f1 /= f2;
    assert!(f1.is_nan());
}

#[test]
fn test_div_assign_inf_divided_by_zero() {
    // Line 1182-1186: other.is_zero() -> set infinite with appropriate sign
    let mut f1 = Fraction::new(1, 0);
    f1 /= Fraction::new(0, 1);
    assert!(f1.is_infinite());
    assert!(*f1.numer() > 0);

    let mut f2 = Fraction::new(-1, 0);
    f2 /= Fraction::new(0, 1);
    assert!(f2.is_infinite());
    assert!(*f2.numer() < 0);
}

#[test]
fn test_div_assign_self_inf() {
    // Line 1191: self.is_infinite() -> return (keep self as inf)
    let mut inf = Fraction::new(1, 0);
    inf /= Fraction::new(2, 1);
    assert!(inf.is_infinite());
}

#[test]
fn test_div_assign_other_inf() {
    // Line 1194-1196: other.is_infinite() -> zero
    let f = Fraction::new(1, 1);
    let result = f / Fraction::new(1, 0);
    assert!(result.is_zero());
}

#[test]
fn test_mul_assign_inf_times_zero() {
    // Line 1108: (self.is_infinite() && other.is_zero()) || (self.is_zero() && other.is_infinite())
    let mut f1 = Fraction::new(1, 0);
    f1 *= Fraction::new(0, 1);
    assert!(f1.is_nan());

    let mut f2 = Fraction::new(0, 1);
    f2 *= Fraction::new(1, 0);
    assert!(f2.is_nan());
}

#[test]
fn test_mul_assign_self_zero() {
    // Line 1112: self.is_zero() -> set zero
    let mut f = Fraction::new(0, 1);
    f *= Fraction::new(5, 6);
    assert!(f.is_zero());
}

#[test]
fn test_mul_assign_other_zero() {
    // Line 1112: other.is_zero() -> set zero
    let mut f = Fraction::new(1, 2);
    f *= Fraction::new(0, 1);
    assert!(f.is_zero());
}

#[test]
fn test_mul_assign_both_infinite() {
    // Line 1116: other.is_infinite() or self.is_infinite()
    let mut f1 = Fraction::new(1, 0);
    f1 *= Fraction::new(1, 0);
    assert!(f1.is_infinite());

    let mut f2 = Fraction::new(1, 0);
    f2 *= Fraction::new(-1, 0);
    assert!(f2.is_infinite());
    assert!(*f2.numer() < 0);
}

#[test]
fn test_ord_cmp_equal_denominators() {
    // Line 1064: self.denom == other.denom -> compare numerators directly
    let f1 = Fraction::new(1, 4);
    let f2 = Fraction::new(2, 4);
    assert!(f1 < f2);

    let f3 = Fraction::new(3, 4);
    let f4 = Fraction::new(3, 4);
    assert_eq!(f3, f4);

    let f5 = Fraction::new(5, 4);
    assert!(f5 > f4);
}

#[test]
fn test_forward_op_assign_ref() {
    // Test forward_op_assign macro - lines 1561 and 1571
    let mut f1 = Fraction::new(1, 2);
    let f2 = Fraction::new(1, 3);
    f1 += &f2;
    assert_eq!(f1, Fraction::new(5, 6));

    let mut f3 = Fraction::new(1, 2);
    let val = 1i32;
    f3 += &val;
    assert_eq!(f3, Fraction::new(3, 2));
}

#[test]
fn test_add_assign_scalar_same_denominator_one() {
    // Line 1525: self.denom == One::one() path
    let mut f = Fraction::new(3, 1);
    f += 2;
    assert_eq!(f, Fraction::new(5, 1));
}

#[test]
fn test_sub_assign_scalar_same_denominator_one() {
    // Line 1475: self.denom == One::one() path
    let mut f = Fraction::new(5, 1);
    f -= 2;
    assert_eq!(f, Fraction::new(3, 1));
}

#[test]
fn test_fraction_is_zero_edge_cases() {
    // Line 280: numer.is_zero() && !denom.is_zero()
    let zero = Fraction::new(0, 5);
    assert!(zero.is_zero());
    assert!(!zero.is_nan());
    assert!(!zero.is_infinite());

    // Edge case: zero/zero is NaN, not zero
    let nan = Fraction::new(0, 0);
    assert!(!nan.is_zero());
}

#[test]
fn test_fraction_clone_and_copy() {
    let f1 = Fraction::new(3, 4);
    let f2 = f1;
    assert_eq!(f1, f2);

    let f3 = f1;
    assert_eq!(f1, f3);
}

// ============================================================================
// Fraction<i8> coverage tests
// ============================================================================

#[test]
fn test_i8_construction() {
    let f = Fraction::new(1i8, 2i8);
    assert_eq!(f, Fraction::new(1i8, 2));

    let f_raw = Fraction::new_raw(3i8, 4i8);
    assert_eq!(*f_raw.numer(), 3i8);
    assert_eq!(*f_raw.denom(), 4i8);

    let f_def: Fraction<i8> = Fraction::default();
    assert!(f_def.is_zero());

    let f_zero = Fraction::<i8>::zero();
    assert!(f_zero.is_zero());
    assert_eq!(*f_zero.numer(), 0i8);
    assert_eq!(*f_zero.denom(), 1i8);

    let f_one = Fraction::<i8>::one();
    assert!(f_one.is_one());
    assert_eq!(*f_one.numer(), 1i8);
    assert_eq!(*f_one.denom(), 1i8);
}

#[test]
fn test_i8_special_values() {
    let zero: Fraction<i8> = Fraction::new(0, 1);
    assert!(zero.is_zero());
    assert!(!zero.is_infinite());
    assert!(!zero.is_nan());

    let inf: Fraction<i8> = Fraction::new(1, 0);
    assert!(inf.is_infinite());

    let neg_inf: Fraction<i8> = Fraction::new(-1, 0);
    assert!(neg_inf.is_infinite());

    let nan: Fraction<i8> = Fraction::new(0, 0);
    assert!(nan.is_nan());
}

#[test]
fn test_i8_setters() {
    let mut f: Fraction<i8> = Fraction::new(1, 2);

    f.set_zero();
    assert!(f.is_zero());

    f.set_one();
    assert!(f.is_one());

    f.set_infinite();
    assert!(f.is_infinite());

    f.set_nan();
    assert!(f.is_nan());
}

#[test]
fn test_i8_arithmetic() {
    let f1: Fraction<i8> = Fraction::new(1, 2);
    let f2: Fraction<i8> = Fraction::new(1, 3);

    assert_eq!(f1 + f2, Fraction::new(5i8, 6));
    assert_eq!(f1 - f2, Fraction::new(1i8, 6));
    assert_eq!(f1 * f2, Fraction::new(1i8, 6));
    assert_eq!(f1 / f2, Fraction::new(3i8, 2));
    assert_eq!(-f1, Fraction::new(-1i8, 2));
    assert_eq!(f1.abs(), Fraction::new(1i8, 2));
}

#[test]
fn test_i8_comparison() {
    let f1: Fraction<i8> = Fraction::new(1, 2);
    let f2: Fraction<i8> = Fraction::new(1, 3);

    assert!(f1 > f2);
    assert!(f2 < f1);
    assert_eq!(f1, Fraction::new(2i8, 4));

    assert_eq!(Fraction::from(3i8), 3i8);
    assert_eq!(3i8, Fraction::from(3i8));
    assert!(Fraction::from(3i8) > 1i8);
    assert!(1i8 < Fraction::from(3i8));
}

#[test]
fn test_i8_compound_assign() {
    let mut f: Fraction<i8> = Fraction::new(1, 2);
    f += Fraction::new(1i8, 3);
    assert_eq!(f, Fraction::new(5i8, 6));
    f -= Fraction::new(1i8, 6);
    assert_eq!(f, Fraction::new(2i8, 3));
    f *= Fraction::new(3i8, 2);
    assert_eq!(f, Fraction::new(1i8, 1));
    f /= Fraction::new(2i8, 1);
    assert_eq!(f, Fraction::new(1i8, 2));
}

#[test]
fn test_i8_scalar_assign() {
    let mut f: Fraction<i8> = Fraction::new(1, 2);
    f += 1i8;
    assert_eq!(f, Fraction::new(3i8, 2));
    f -= 1i8;
    assert_eq!(f, Fraction::new(1i8, 2));
    f *= 2i8;
    assert_eq!(f, Fraction::new(1i8, 1));
    f /= 2i8;
    assert_eq!(f, Fraction::new(1i8, 2));
}

#[test]
fn test_i8_forward_op_assign_ref() {
    let mut f: Fraction<i8> = Fraction::new(1, 2);
    let g = Fraction::new(1i8, 3);
    f += &g;
    assert_eq!(f, Fraction::new(5i8, 6));

    let mut f2: Fraction<i8> = Fraction::new(1, 2);
    let val = 1i8;
    f2 += &val;
    assert_eq!(f2, Fraction::new(3i8, 2));
}

// ============================================================================
// From/TryFrom coverage tests
// ============================================================================

#[test]
fn test_from_i8_to_i32() {
    let f: Fraction<i32> = Fraction::from(5i8);
    assert_eq!(f, Fraction::new(5i32, 1));
}

#[test]
fn test_from_u8_to_i32() {
    let f: Fraction<i32> = Fraction::from(5u8);
    assert_eq!(f, Fraction::new(5i32, 1));
}

#[test]
fn test_try_from_i64_to_i32() {
    use core::convert::TryFrom;
    let f_i64 = Fraction::new(5i64, 1i64);
    let f_i32 = Fraction::<i32>::try_from(f_i64).unwrap();
    assert_eq!(f_i32, Fraction::new(5i32, 1));
}

#[test]
fn test_try_from_i128_to_i64() {
    use core::convert::TryFrom;
    let f_i128 = Fraction::new(5i128, 1i128);
    let f_i64 = Fraction::<i64>::try_from(f_i128).unwrap();
    assert_eq!(f_i64, Fraction::new(5i64, 1));
}

// ============================================================================
// Fraction<i128> coverage tests
// ============================================================================

#[test]
fn test_i128_construction() {
    let f = Fraction::new(1i128, 2i128);
    assert_eq!(f, Fraction::new(1i128, 2));

    let f_raw = Fraction::new_raw(3i128, 4i128);
    assert_eq!(*f_raw.numer(), 3i128);
    assert_eq!(*f_raw.denom(), 4i128);
}

#[test]
fn test_i128_special_values() {
    let inf: Fraction<i128> = Fraction::new(1, 0);
    assert!(inf.is_infinite());

    let neg_inf: Fraction<i128> = Fraction::new(-1, 0);
    assert!(neg_inf.is_infinite());

    let nan: Fraction<i128> = Fraction::new(0, 0);
    assert!(nan.is_nan());
}

#[test]
fn test_i128_normalization() {
    // Exercise normalize/reduce for i128 Fraction
    let mut f = Fraction::new_raw(4i128, 6i128);
    f.normalize();
    assert_eq!(f, Fraction::new(2i128, 3));
}
