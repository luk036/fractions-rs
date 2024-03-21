//! Fraction numbers
//!
//! ## Compatibility
//!
//! The `fractions-rs` crate is tested for rustc 1.31 and greater.

#![no_std]
// Fraction ops often use other "suspicious" ops
#![allow(clippy::suspicious_arithmetic_impl)]
#![allow(clippy::suspicious_op_assign_impl)]

pub mod fractions;
pub use crate::fractions::Fraction;
pub use crate::fractions::{const_abs, const_gcd};

use core::ops::{Add, Mul, Sub};

/// The function `archimedes` calculates the area of a triangle using Archimedes' formula with the
/// lengths of the three sides provided as `Fraction<i64>` values.
///
/// Arguments:
///
/// * `q_1`: Represents the length of the first side of the triangle.
/// * `q_2`: The parameters `q_1`, `q_2`, and `q_3` represent the lengths of the sides of a triangle. In
///          the context of Archimedes' formula for the area of a triangle, `q_1`, `q_2`, and `q_3`
/// * `q_3`: The parameter `q_3` represents the length of the third side of the triangle.
///
/// Returns:
///
/// The function `archimedes` returns the area of a triangle computed using Archimedes' formula, given
/// the lengths of the 3 sides.
///
#[inline]
pub fn archimedes<T>(q_1: &T, q_2: &T, q_3: &T) -> T
where
    T: Copy + Add<Output = T> + Sub<Output = T> + Mul<Output = T> + From<i32>,
{
    let temp = *q_1 + *q_2 - *q_3;
    T::from(4) * *q_1 * *q_2 - temp * temp
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_integer::gcd;
    use quickcheck_macros::quickcheck;

    #[test]
    fn it_works() {
        let result: i32 = const_gcd(4, -6);
        assert_eq!(result, 2);

        let result = gcd(4, -6);
        assert_eq!(result, 2);

        let f = Fraction::new(30, -40);
        assert_eq!(f, Fraction::new(-3, 4));

        let h = Fraction::from(30);
        assert_eq!(h, Fraction::new(30, 1));

        let g = Fraction::<i32>::default();
        assert_eq!(g, Fraction::new(0, 1));
    }

    #[test]
    fn test_cross() {
        let f = Fraction::new(30, 40);
        let h = Fraction::from(3);
        let result = Fraction::cross(&f, &h);
        assert_eq!(result, -9);
        assert_eq!(h, 3);
        // assert_eq!(result, 30);
    }

    #[test]
    fn test_ordering() {
        let f = Fraction::new(3, 4);
        assert!(f != 1i32);
        assert!(1i32 != f);
        assert!(f < 1i32);
        assert!(1i32 > f);
        // assert_eq!(result, 30);
    }

    #[test]
    fn test_mul_div_assign() {
        let mut f = Fraction::new(3, 4);
        let g = Fraction::new(5, 6);
        f *= g;
        assert_eq!(f, Fraction::new(5, 8));
        f /= g;
        assert_eq!(f, Fraction::new(3, 4));
        f *= 2;
        assert_eq!(f, Fraction::new(3, 2));
        f /= 2;
        assert_eq!(f, Fraction::new(3, 4));
        f /= 0;
        assert_eq!(f, Fraction::new(1, 0));
        assert_eq!(-g, Fraction::new(-5, 6));
    }

    #[test]
    fn test_add_sub_assign() {
        let mut f = Fraction::new(3, 4);
        let g = Fraction::new(5, 6);
        f -= g;
        assert_eq!(f, Fraction::new(-1, 12));
        f += g;
        assert_eq!(f, Fraction::new(3, 4));
        f -= 2;
        assert_eq!(f, Fraction::new(-5, 4));
        f += 2;
        assert_eq!(f, Fraction::new(3, 4));
    }

    #[test]
    fn test_mul_div() {
        let f = Fraction::new(3, 4);
        let g = Fraction::new(5, 6);
        assert_eq!(f * g, Fraction::new(5, 8));
        assert_eq!(f / g, Fraction::new(9, 10));
        assert_eq!(f * 2, Fraction::new(3, 2));
        assert_eq!(f / 2, Fraction::new(3, 8));
    }

    #[test]
    fn test_add_sub() {
        let f = Fraction::new(3, 4);
        let g = Fraction::new(5, 6);
        assert_eq!(f - g, Fraction::new(-1, 12));
        assert_eq!(f + g, Fraction::new(19, 12));
        assert_eq!(f - 2, Fraction::new(-5, 4));
        assert_eq!(f + 2, Fraction::new(11, 4));
    }

    #[test]
    fn test_abs() {
        let f = Fraction::new(-3, 4);
        assert_eq!(f.abs(), Fraction::new(3, 4));
    }

    #[test]
    fn test_neg() {
        let f = Fraction::new(-3, 4);
        assert_eq!(-f, f.abs());
    }

    // #[test]
    // fn test_signum() {
    //     let f = Fraction::new(-3, 4);
    //     assert_eq2(f.signum(), -1);
    //     assert_eq2(Fraction::<i8>::default().signum(), 0);
    // }

    #[test]
    fn test_special() {
        let zero = Fraction::new(0, 1);
        let infp = Fraction::new(1, 0);
        let infn = Fraction::new(-1, 0);
        let pos = Fraction::new(1, 40);
        let neg = Fraction::new(-1, 2);
        assert!(infn < neg);
        assert!(neg < zero);
        assert!(zero < pos);
        assert!(pos < infp);
        assert!(infn < infp);

        let nan = Fraction::new(0, 0);
        assert_eq!(infn * neg, infp);
        assert_eq!(infn * pos, infn);
        assert_eq!(infp * zero, nan);
        assert_eq!(infn * zero, nan);
        assert_eq!(infp / infp, nan);
        assert_eq!(infp + infp, infp);
        assert_eq!(infp - infp, nan);
        assert_eq!(infp - pos, infp);
        assert_eq!(infn + pos, infn);
    }

    #[quickcheck]
    fn check_eq(numer: u32, denom: u32) -> bool {
        let p = Fraction::new(numer as i32, denom as i32);
        p == p
    }

    #[quickcheck]
    fn check_neg(numer: u32, denom: u32) -> bool {
        let p = Fraction::new(numer as i32, denom as i32);
        p == -(-p)
    }

    #[quickcheck]
    fn check_reciprocal(numer: i32) -> bool {
        let mut p = Fraction::new(numer / 2, 10000);
        let q = p;
        p.reciprocal();
        p.reciprocal();
        p == q
    }

    #[quickcheck]
    fn check_default(numer: u32, denom: u32) -> bool {
        let p = Fraction::new(numer as i32, denom as i32);
        let zero = Fraction::<i32>::default();
        p == p + zero
    }

    #[quickcheck]
    fn check_mul(n1: u16, d2: u16) -> bool {
        let p = Fraction::new(n1 as i32, 2000000000);
        let q = Fraction::new(2000000000, d2 as i32);
        p * q == q * p
    }

    #[quickcheck]
    fn check_add(d1: u32, d2: u32) -> bool {
        let p = Fraction::new(2000000001_i128, d1 as i128);
        let q = Fraction::new(2000000009_i128, d2 as i128);
        p + q == q + p
    }

    #[quickcheck]
    fn check_add_sub(n1: u32, n2: u32) -> bool {
        let p = Fraction::new(n1 as i128, 2000000001_i128);
        let q = Fraction::new(n2 as i128, 2000000009_i128);
        p == (p + q) - q
    }

    #[test]
    fn test_archimedes4() {
        let q_1 = Fraction::<i32>::new(1, 2);
        let q_2 = Fraction::<i32>::new(1, 4);
        let q_3 = Fraction::<i32>::new(1, 6);
        assert_eq!(archimedes(&q_1, &q_2, &q_3), Fraction::<i32>::new(23, 144));
    }
}
