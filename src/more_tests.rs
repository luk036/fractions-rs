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
