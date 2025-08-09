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
