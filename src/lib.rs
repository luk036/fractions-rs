//! Fraction numbers
//!
//! ## Compatibility
//!
//! The `fractions-rs` crate is tested for rustc 1.31 and greater.

// #![no_std]
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
///   the context of Archimedes' formula for the area of a triangle, `q_1`, `q_2`, and `q_3`
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

    #[test]
    fn test_archimedes4() {
        let q_1 = Fraction::<i32>::new(1, 2);
        let q_2 = Fraction::<i32>::new(1, 4);
        let q_3 = Fraction::<i32>::new(1, 6);
        assert_eq!(archimedes(&q_1, &q_2, &q_3), Fraction::<i32>::new(23, 144));
    }

    #[test]
    fn test_archimedes5() {
        let q_1 = Fraction::<i64>::new(1, 2);
        let q_2 = Fraction::<i64>::new(1, 4);
        let q_3 = Fraction::<i64>::new(1, 6);
        assert_eq!(archimedes(&q_1, &q_2, &q_3), Fraction::<i64>::new(23, 144));
    }
}

#[cfg(test)]
mod more_tests;
