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