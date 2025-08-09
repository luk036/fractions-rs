#![allow(unused_imports)]
#![allow(dead_code)]

#[cfg(test)]
use core::hash;
// use core::iter::{Product, Sum};
use core::ops::{Add, Div, Mul, Neg, Rem, Sub};
use core::ops::{AddAssign, DivAssign, MulAssign, SubAssign};

// use core::str::FromStr;
use num_integer::gcd;
use num_integer::Integer;
use num_traits::{Inv, Num, NumAssign, One, Signed, Zero};
// #[cfg(feature = "std")]
// use std::error::Error;
use core::cmp::Ordering;
use core::mem; // for swap

use core::fmt;
use core::fmt::{Binary, Display, Formatter, LowerExp, LowerHex, Octal, UpperExp, UpperHex};
use core::hash::{Hash, Hasher};

// #[inline]
// pub const fn const_abs2<T>(a: T) -> T
// where T: Integer + Neg<Output = T> + Zero + ~const std::cmp::PartialOrd,
// {
//     if a < Zero::zero() { -a } else { a }
// }

/// The function `const_abs` returns the absolute value of an integer.
///
/// Arguments:
///
/// * `a`: The parameter `a` is of type `i32`, which means it is an integer.
///
/// Returns:
///
/// The function `const_abs` returns the absolute value of the input `a`.
///
/// Examples:
///
/// ```rust
/// use fractions::const_abs;
/// assert_eq!(const_abs(-10), 10);
/// assert_eq!(const_abs(10), 10);
/// ```
#[inline]
pub fn const_abs<T: Integer + Neg<Output = T>>(a: T) -> T {
    if a < Zero::zero() {
        -a
    } else {
        a
    }
}

/// The function calculates the greatest common divisor (GCD) of two integers using recursion.
///
/// Arguments:
///
/// * `m`: An integer representing the first number for which we want to find the greatest common
///        divisor (GCD).
/// * `n`: The parameter `n` represents the second number in the pair for which we want to find the
///        greatest common divisor (GCD).
///
/// Returns:
///
/// The function `gcd_recur` returns the greatest common divisor (GCD) of the two input integers `m` and
/// `n`.
#[inline]
fn gcd_recur<T: Integer + Neg<Output = T> + Copy>(m: T, n: T) -> T {
    if n == Zero::zero() {
        const_abs(m)
    } else {
        gcd_recur(n, m % n)
    }
}

/// The function `const_gcd` calculates the greatest common divisor (GCD) of two integers using
/// recursion.
///
/// Arguments:
///
/// * `m`: The parameter `m` represents the first integer for which we want to find the greatest common
///        divisor (GCD).
/// * `n`: The parameter `n` represents the first number for which we want to find the greatest common
///        divisor (GCD).
///
/// Returns:
///
/// The function `const_gcd` returns an `i32` value, which represents the greatest common divisor of the
/// two input integers `m` and `n`.
///
/// Examples:
///
/// ```rust
/// use fractions::const_gcd;
/// assert_eq!(const_gcd(30, -40), 10);
/// assert_eq!(const_gcd(30, 40), 10);
/// ```
#[inline]
pub fn const_gcd<T: Integer + Neg<Output = T> + Copy>(m: T, n: T) -> T {
    if m == Zero::zero() {
        const_abs(n)
    } else {
        gcd_recur(m, n)
    }
}

#[cfg(test)]
#[test]
fn test_gcd_recur() {
    assert_eq!(gcd_recur(30, -40), 10);
    assert_eq!(gcd_recur(30, 40), 10);
}

/// The above code defines a generic Fraction struct in Rust with numerator and denominator fields.
///
/// Properties:
///
/// * `numer`: The `numer` property represents the numerator portion of the `Fraction` object. It is of type
///            `T`, which is a generic type parameter that must implement the `Integer` trait. The numerator is the
///            top part of a fraction, representing the number of equal parts being considered.
/// * `denom`: The `denom` property represents the denominator portion of the `Fraction` object. The
///            denominator is the number below the line in a fraction and represents the total number of equal
///            parts into which the whole is divided.
#[derive(PartialEq, Eq, Copy, Clone, Hash, Debug)]
#[allow(missing_docs)]
pub struct Fraction<T> {
    /// numerator portion of the Fraction object
    pub numer: T,
    /// denominator portion of the Fraction object
    pub denom: T,
}

/// These method are `const` for Rust 1.31 and later.
impl<T> Fraction<T> {
    /// Creates a `Fraction` without checking for `denom == 0` or reducing.
    ///
    /// **There are several methods that will panic if used on a `Fraction` with
    /// `denom == 0`.**
    ///
    /// Examples:
    ///
    /// ```rust
    /// use fractions::Fraction;
    /// let f = Fraction::new_raw(10, 2); // 5/1
    /// assert_eq!(f.numer(), &10);
    /// assert_eq!(f.denom(), &2);
    /// ```
    #[inline]
    pub const fn new_raw(numer: T, denom: T) -> Fraction<T> {
        Fraction { numer, denom }
    }

    /// Gets an immutable reference to the numerator.
    #[inline]
    pub const fn numer(&self) -> &T {
        &self.numer
    }

    /// Gets an immutable reference to the denominator.
    #[inline]
    pub const fn denom(&self) -> &T {
        &self.denom
    }
}

// Constants
impl<T: Clone + Integer> Fraction<T> {
    /// Creates a `Fraction` with a numerator of 0 and a denominator of 1.
    /// This represents the number zero as a fraction.
    #[inline]
    pub fn zero() -> Fraction<T> {
        Fraction::new_raw(Zero::zero(), One::one())
    }

    /// Checks if the fraction is equal to zero.
    ///
    /// Returns `true` if the numerator is zero and the denominator is non-zero.
    #[inline]
    pub fn is_zero(&self) -> bool {
        self.numer.is_zero() && !self.denom.is_zero()
    }

    /// Sets the fraction to zero by setting the numerator to zero and
    /// the denominator to one.
    #[inline]
    pub fn set_zero(&mut self) {
        self.numer.set_zero();
        self.denom.set_one();
    }

    /// Checks if the fraction is in normal form, meaning the numerator and
    /// denominator are not zero.
    ///
    /// Returns `true` if neither the numerator nor denominator are zero.
    #[inline]
    pub fn is_normal(&self) -> bool {
        !(self.numer.is_zero() || self.denom.is_zero())
    }

    /// Checks if the fraction represents infinity.
    ///
    /// Returns `true` if the numerator is non-zero and the denominator is zero.
    #[inline]
    pub fn is_infinite(&self) -> bool {
        !self.numer.is_zero() && self.denom.is_zero()
    }

    /// Checks if the fraction represents NaN (not a number).
    ///
    /// Returns `true` if both the numerator and denominator are zero.
    #[inline]
    pub fn is_nan(&self) -> bool {
        self.numer.is_zero() && self.denom.is_zero()
    }

    /// Sets the fraction to NaN (not a number) by setting both the
    /// numerator and denominator to zero.
    #[inline]
    pub fn set_nan(&mut self) {
        self.numer.set_zero();
        self.denom.set_zero();
    }

    /// Sets the fraction to infinity by setting the numerator to one and
    /// the denominator to zero.
    #[inline]
    pub fn set_infinite(&mut self) {
        self.numer.set_one();
        self.denom.set_zero();
    }
}

impl<T: Clone + Integer> Fraction<T> {
    #[inline]
    pub fn one() -> Fraction<T> {
        Fraction::new_raw(One::one(), One::one())
    }

    #[inline]
    pub fn is_one(&self) -> bool {
        self.numer == self.denom
    }

    #[inline]
    pub fn set_one(&mut self) {
        self.numer.set_one();
        self.denom.set_one();
    }
}

impl<T> Fraction<T>
where
    T: Integer + Zero + One + Neg<Output = T> + DivAssign + Copy,
{
    /// The `new` function creates a new `Fraction` object and normalizes it.
    ///
    /// Arguments:
    ///
    /// * `numer`: The `numer` parameter represents the numerator of the fraction. It is the number above
    ///            the fraction line.
    /// * `denom`: The parameter `denom` represents the denominator of the fraction. It is the number below
    ///            the line in a fraction and represents the total number of equal parts into which the whole is
    ///            divided.
    ///
    /// Returns:
    ///
    /// The `new` function returns a new instance of the `Fraction` struct.
    ///
    /// Examples:
    ///
    /// ```rust
    /// use fractions::Fraction;
    /// let f = Fraction::new(30, -40);
    /// assert_eq!(f, Fraction::new(-3, 4));
    /// ```
    #[inline]
    pub fn new(numer: T, denom: T) -> Self {
        let mut res = Fraction { numer, denom };
        res.normalize();
        res
    }

    /// The `normalize` function in Rust normalizes a value to a canonical form by ensuring that the
    /// denominator is always non-negative and co-prime with the numerator.
    ///
    /// Returns:
    ///
    /// The `normalize` function returns a value of type `T`.
    ///
    /// Examples:
    ///
    /// ```rust
    /// use fractions::Fraction;
    /// let mut f = Fraction { numer: 30, denom: -40 };
    /// assert_eq!(f.normalize(), 10);
    /// assert_eq!(f, Fraction::new(-3, 4));
    /// ```
    #[inline]
    pub fn normalize(&mut self) -> T {
        self.keep_denom_positive();
        self.reduce()
    }

    // #[inline]
    // pub fn abs(self) -> Self {
    //     let mut res = self;
    //     res.numer = const_abs(res.numer);
    //     res
    // }
}

impl<T> Fraction<T>
where
    T: Integer + Zero + One + Neg<Output = T> + Copy + Signed,
{
    /// The `abs` function in Rust returns the absolute of a `Fraction` object.
    ///
    /// Examples:
    ///
    /// ```rust
    /// use fractions::Fraction;
    /// let mut f = Fraction::new(-3, 4);
    ///
    /// assert_eq!(f.abs(), Fraction::new(3, 4));
    /// ```
    #[inline]
    pub fn abs(&self) -> Fraction<T> {
        if self.is_negative() {
            -*self
        } else {
            *self
        }
    }

    #[inline]
    fn signum(&self) -> Fraction<T> {
        if self.is_positive() {
            Self::one()
        } else if self.is_zero() {
            Self::zero()
        } else {
            -Self::one()
        }
    }

    #[inline]
    fn is_positive(&self) -> bool {
        self.numer.is_positive()
    }

    #[inline]
    fn is_negative(&self) -> bool {
        self.numer.is_negative()
    }
}

// String conversions
// macro_rules! impl_formatting {
//     ($fmt_trait:ident, $prefix:expr, $fmt_str:expr, $fmt_alt:expr) => {
//         impl<T: $fmt_trait + Clone + Integer> $fmt_trait for Fraction<T> {
//             #[cfg(feature = "std")]
//             fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
//                 let pre_pad = if self.denom.is_one() {
//                     format!($fmt_str, self.numer)
//                 } else {
//                     if f.alternate() {
//                         format!(concat!($fmt_str, "/", $fmt_alt), self.numer, self.denom)
//                     } else {
//                         format!(concat!($fmt_str, "/", $fmt_str), self.numer, self.denom)
//                     }
//                 };
//                 // TODO: replace with strip_prefix, when stabalized
//                 let (pre_pad, non_negative) = {
//                     if pre_pad.starts_with("-") {
//                         (&pre_pad[1..], false)
//                     } else {
//                         (&pre_pad[..], true)
//                     }
//                 };
//                 f.pad_integral(non_negative, $prefix, pre_pad)
//             }
//             #[cfg(not(feature = "std"))]
//             fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
//                 let plus = if f.sign_plus() && self.numer >= T::zero() {
//                     "+"
//                 } else {
//                     ""
//                 };
//                 if self.denom.is_one() {
//                     if f.alternate() {
//                         write!(f, concat!("{}", $fmt_alt), plus, self.numer)
//                     } else {
//                         write!(f, concat!("{}", $fmt_str), plus, self.numer)
//                     }
//                 } else {
//                     if f.alternate() {
//                         write!(
//                             f,
//                             concat!("{}", $fmt_alt, "/", $fmt_alt),
//                             plus, self.numer, self.denom
//                         )
//                     } else {
//                         write!(
//                             f,
//                             concat!("{}", $fmt_str, "/", $fmt_str),
//                             plus, self.numer, self.denom
//                         )
//                     }
//                 }
//             }
//         }
//     };
// }

// impl_formatting!(Display, "", "{}", "{:#}");
// impl_formatting!(Octal, "0o", "{:o}", "{:#o}");
// impl_formatting!(Binary, "0b", "{:b}", "{:#b}");
// impl_formatting!(LowerHex, "0x", "{:x}", "{:#x}");
// impl_formatting!(UpperHex, "0x", "{:X}", "{:#X}");
// impl_formatting!(LowerExp, "", "{:e}", "{:#e}");
// impl_formatting!(UpperExp, "", "{:E}", "{:#E}");

impl<T: Integer + Zero + One + DivAssign + Copy> Fraction<T> {
    /// The `reduce` function normalizes a fraction to its canonical form by dividing both the
    /// numerator and denominator by their greatest common divisor.
    ///
    /// Returns:
    ///
    /// The function `reduce` returns a value of type `T`.
    #[inline]
    pub fn reduce(&mut self) -> T {
        let common = gcd(self.numer, self.denom);
        if common != One::one() && common != Zero::zero() {
            self.numer /= common;
            self.denom /= common;
        }
        common
    }
}

impl<T: Integer + Zero + Neg<Output = T> + Ord + Copy> Fraction<T> {
    /// The `keep_denom_positive` function in Rust normalizes a fraction to a canonical form by ensuring that the
    /// denominator is always non-negative.
    #[inline]
    pub fn keep_denom_positive(&mut self) {
        if self.denom < Zero::zero() {
            self.numer = -self.numer;
            self.denom = -self.denom;
        }
    }

    /// The `reciprocal` function swaps the numerator and denominator of a fraction and normalizes it.
    ///
    /// Examples:
    ///
    /// ```rust
    /// use fractions::Fraction;
    /// let mut f = Fraction::new(30, -40);
    /// f.reciprocal();
    ///
    /// assert_eq!(f, Fraction::new(-4, 3));
    /// ```
    #[inline]
    pub fn reciprocal(&mut self) {
        mem::swap(&mut self.numer, &mut self.denom);
        self.keep_denom_positive();
    }
}

impl<T: Integer + One> From<T> for Fraction<T> {
    /// The `from` function in Rust creates a `Fraction` struct from an integer.
    ///
    /// Arguments:
    ///
    /// * `numer`: The `numer` parameter is an integer value that will be used to create a new `Fraction` object.
    ///
    /// Returns:
    ///
    /// The `from` function returns a `Fraction` struct.
    ///
    /// Examples:
    ///
    /// ```rust
    /// use fractions::Fraction;
    /// let mut f = Fraction::<i32>::from(3);
    /// assert_eq!(f, Fraction::<i32>::new(3, 1));
    /// ```
    #[inline]
    fn from(numer: T) -> Self {
        Fraction {
            numer,
            denom: One::one(),
        }
    }
}

impl From<i32> for Fraction<i64> {
    /// The `from` function in Rust creates a `Fraction` struct from an integer.
    ///
    /// Arguments:
    ///
    /// * `numer`: The `numer` parameter is an integer value that will be used to create a new `Fraction` object.
    ///
    /// Returns:
    ///
    /// The `from` function returns a `Fraction` struct.
    ///
    /// Examples:
    ///
    /// ```rust
    /// use fractions::Fraction;
    /// let mut f = Fraction::<i64>::from(3);
    /// assert_eq!(f, Fraction::<i64>::new(3, 1));
    /// ```
    #[inline]
    fn from(i: i32) -> Self {
        Fraction {
            numer: i as i64,
            denom: One::one(),
        }
    }
}

impl<T: Integer + One + Zero> Default for Fraction<T> {
    /// The `default` function returns a default `Fraction` object with numerator 0 and denominator 1.
    ///
    /// Returns:
    ///
    /// The `default()` function is returning a `Fraction` object with the numerator set to zero and the
    /// denominator set to one.
    ///
    /// Examples:
    ///
    /// ```rust
    /// use fractions::Fraction;
    /// let mut f = Fraction::<i32>::default();
    /// assert_eq!(f, Fraction::zero());
    /// ```
    #[inline]
    fn default() -> Self {
        Fraction {
            numer: Zero::zero(),
            denom: One::one(),
        }
    }
}

// From integer
// impl<T> From<T> for Fraction<T>
// where
//     T: Clone + Integer,
// {
//     fn from(x: T) -> Fraction<T> {
//         Fraction::new_raw(x, One::one())
//     }
// }

impl<T: Integer + Copy> Fraction<T> {
    /// The `cross` function calculates the cross product of two values.
    ///
    /// Arguments:
    ///
    /// * `rhs`: The parameter `rhs` is a reference to another object of the same type as `self`.
    ///
    /// Returns:
    ///
    /// The cross product of two values of type T.
    ///
    /// Example:
    /// ```rust
    /// use fractions::Fraction;
    /// let f1 = Fraction::new(3, 4);
    /// let f2 = Fraction::new(-5, 6);
    /// let res = f1.cross(&f2);
    /// assert_eq!(res, 38);
    /// ```
    #[inline]
    pub fn cross(&self, rhs: &Self) -> T {
        self.numer * rhs.denom - self.denom * rhs.numer
    }
}

// impl<T: Integer + Neg<Output = T>> Neg for Fraction<T> {
//     type Output = Fraction<T>;

//     /// The `neg` function in Rust returns the negation of a `Fraction` object.
//     ///
//     /// Examples:
//     ///
//     /// ```rust
//     /// use fractions::Fraction;
//     /// let mut f = Fraction::new(3, 4);
//     ///
//     /// assert_eq!(-f, Fraction::new(-3, 4));
//     /// ```
//     #[inline]
//     fn neg(self) -> Self::Output {
//         let mut res = self;
//         res.numer = -res.numer;
//         res
//     }
// }

impl<T> Neg for Fraction<T>
where
    T: Integer + Neg<Output = T>,
{
    type Output = Fraction<T>;

    /// The `neg` function in Rust returns the negation of a `Fraction` object.
    ///
    /// Examples:
    ///
    /// ```rust
    /// use fractions::Fraction;
    /// let mut f = Fraction::new(3, 4);
    ///
    /// assert_eq!(-f, Fraction::new(-3, 4));
    /// ```
    #[inline]
    fn neg(self) -> Fraction<T> {
        Fraction::new_raw(-self.numer, self.denom)
    }
}

impl<T> Neg for &Fraction<T>
where
    T: Clone + Integer + Neg<Output = T>,
{
    type Output = Fraction<T>;

    /// Negates the given immutable fraction reference by cloning and negating
    /// the clone.
    ///
    /// Example:
    ///
    /// ```rust
    /// use fractions::Fraction;
    /// let f = Fraction::new(3, 4);
    /// let g = -f;
    /// assert_eq!(g, Fraction::new(-3, 4));
    /// ```
    #[inline]
    fn neg(self) -> Fraction<T> {
        -self.clone()
    }
}

impl<T> Inv for Fraction<T>
where
    T: Clone + Integer + Neg<Output = T> + Copy,
{
    type Output = Fraction<T>;

    /// The `inv` function inverts the `Fraction` object in place.
    ///
    /// It clones the fraction, calls `reciprocal` on the clone to invert it,
    /// and returns the inverted fraction, leaving the original unchanged.
    ///
    /// Example:
    ///
    /// ```rust
    /// use num_traits::ops::inv::Inv;
    /// use fractions::Fraction;
    /// let f = Fraction::new(-3, 4);
    /// let inv_f = f.inv();
    /// assert_eq!(inv_f, Fraction::new(-4, 3));
    /// ```
    #[inline]
    fn inv(self) -> Fraction<T> {
        let mut res = self;
        res.reciprocal();
        res
    }
}

impl<T: Integer + PartialEq + Copy + DivAssign> PartialEq<T> for Fraction<T> {
    /// The above code is defining a Rust documentation comment for a function called `Equal to`. It
    /// provides examples of how to use the function to check if a `Fraction` object is equal to a given
    /// value. The examples demonstrate creating `Fraction` objects and using the `==` and `!=`
    /// operators to compare them with the given value.
    ///
    /// Examples:
    ///
    /// ```rust
    /// use fractions::Fraction;
    /// let f = Fraction::from(3);
    /// let g = Fraction::new(3, 4);
    ///
    /// assert!(f == 3);
    /// assert!(g != 3);
    /// ```
    #[inline]
    fn eq(&self, other: &T) -> bool {
        self.denom == One::one() && self.numer == *other
    }
}
// impl<T: Num + Eq + Clone> Eq for Fraction<T> {}

impl<T: Integer + PartialOrd + Copy + DivAssign> PartialOrd<T> for Fraction<T> {
    /// The `partial_cmp` function compares a `Fraction` object with another object of type `T` and
    /// returns an `Option<Ordering>` indicating the relationship between the two objects.
    ///
    /// Arguments:
    ///
    /// * `other`: The `other` parameter is a reference to a value of type `T`. It is used to compare
    ///            with the current `Fraction` instance (`self`) to determine the ordering relationship between
    ///            them.
    ///
    /// Returns:
    ///
    /// The `partial_cmp` function returns an `Option<Ordering>`.
    ///
    /// Examples:
    ///
    /// ```rust
    /// use fractions::Fraction;
    /// let f = Fraction::new(3, 4);
    ///
    /// assert!(f < 1);
    /// assert!(f > 0);
    /// ```
    fn partial_cmp(&self, other: &T) -> Option<Ordering> {
        if self.denom == One::one() || *other == Zero::zero() {
            return self.numer.partial_cmp(other);
        }
        let mut lhs = Self {
            numer: self.numer,
            denom: *other,
        };
        let rhs = self.denom;
        lhs.reduce();
        lhs.numer.partial_cmp(&(lhs.denom * rhs))
    }
}

macro_rules! scalar_ord_eq {
    ($($scalar:ident),*) => (
        $(
            impl PartialEq<Fraction<$scalar>> for $scalar {
                /// The function checks if the given fraction is equal to a scalar value.
                ///
                /// Arguments:
                ///
                /// * `other`: A reference to another Fraction object with a scalar type specified by
                ///            the generic parameter .
                ///
                /// Returns:
                ///
                /// A boolean value is being returned.
                #[inline]
                fn eq(&self, other: &Fraction<$scalar>) -> bool {
                    other.denom == 1 as $scalar && other.numer == *self
                }
            }

            impl PartialOrd<Fraction<$scalar>> for $scalar {
                /// The function compares two fractions and returns an ordering between them.
                ///
                /// Arguments:
                ///
                /// * `other`: `other` is a reference to a `Fraction` object with a generic type
                ///            parameter ``.
                ///
                /// Returns:
                ///
                /// an `Option<Ordering>`.
                fn partial_cmp(&self, other: &Fraction<$scalar>) -> Option<Ordering> {
                    if other.denom == 1 as $scalar || *self == 0 as $scalar {
                        return self.partial_cmp(&other.numer);
                    }
                    let mut rhs = Fraction {
                        numer: other.numer.clone(),
                        denom: self.clone(),
                    };
                    let lhs = other.denom.clone();
                    rhs.normalize();
                    (lhs * rhs.denom).partial_cmp(&rhs.numer)
                }
            }
        )*
    );
}

scalar_ord_eq!(i8, i16, i32, i64);

impl<T: Integer + PartialOrd + Copy + DivAssign> PartialOrd for Fraction<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: Integer + Ord + Copy + DivAssign> Ord for Fraction<T> {
    /// The above code is defining a Rust module and documenting the `PartialOrd` trait for a custom
    /// type `Fraction`. It provides an example usage of comparing two `Fraction` instances using the
    /// `>` operator.
    ///
    /// Examples:
    ///
    /// ```rust
    /// use fractions::Fraction;
    /// let f = Fraction::new(3, 4);
    /// let g = Fraction::new(5, 7);
    ///
    /// assert!(f > g);
    /// ```
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        if self.denom == other.denom {
            return self.numer.cmp(&other.numer);
        }
        let mut lhs = Self {
            numer: self.numer,
            denom: other.numer,
        };
        let mut rhs = Self {
            numer: self.denom,
            denom: other.denom,
        };
        lhs.reduce();
        rhs.reduce();
        (lhs.numer * rhs.denom).cmp(&(lhs.denom * rhs.numer))
    }
}

// Op Assign

impl<T> MulAssign for Fraction<T>
where
    T: Integer + Copy + NumAssign + Signed + Neg<Output = T> + Zero + One,
{
    /// The function performs a multiplication assignment operation on two objects of the same type.
    ///
    /// Arguments:
    ///
    /// * `other`: `other` is a reference to another instance of the same type as `self`.
    fn mul_assign(&mut self, other: Self) {
        if self.is_nan() || other.is_nan() {
            self.set_nan();
            return;
        }
        if (self.is_infinite() && other.is_zero()) || (self.is_zero() && other.is_infinite()) {
            self.set_nan();
            return;
        }
        if self.is_zero() || other.is_zero() {
            self.set_zero();
            return;
        }
        if self.is_infinite() || other.is_infinite() {
            if self.is_negative() ^ other.is_negative() {
                self.numer = -T::one();
            } else {
                self.numer = T::one();
            }
            self.denom = T::zero();
            return;
        }

        let mut rhs = other;
        mem::swap(&mut self.numer, &mut rhs.numer);
        self.reduce();
        rhs.reduce();
        self.numer *= rhs.numer;
        self.denom *= rhs.denom;
    }
}

// impl<T> Mul for Fraction<T>
// where
//     T: Integer + Copy + NumAssign + Zero + One,
// {
//     type Output = Self;
//
//     fn mul(self, other: Self) -> Self::Output {
//         let mut res = self;
//         res.mul_assign(other);
//         res
//     }
// }

impl<T> DivAssign for Fraction<T>
where
    T: Integer + Copy + NumAssign + Neg<Output = T> + Zero + One + Signed,
{
    /// The function performs division assignment on a mutable reference to a struct, swapping and
    /// multiplying its numerator and denominator with another struct.
    ///
    /// Arguments:
    ///
    /// * `other`: `other` is a reference to another instance of the same type as `self`.
    fn div_assign(&mut self, other: Self) {
        if self.is_nan() || other.is_nan() {
            self.set_nan();
            return;
        }
        if self.is_infinite() && other.is_infinite() {
            self.set_nan();
            return;
        }
        if self.is_zero() && other.is_zero() {
            self.set_nan();
            return;
        }
        if other.is_zero() {
            if self.is_negative() {
                self.numer = -T::one();
            } else {
                self.numer = T::one();
            }
            self.denom = T::zero();
            return;
        }
        if self.is_infinite() {
            return;
        }
        if other.is_infinite() {
            self.set_zero();
            return;
        }

        let mut rhs = other;
        mem::swap(&mut self.denom, &mut rhs.numer);
        self.normalize();
        rhs.reduce();
        self.numer *= rhs.denom;
        self.denom *= rhs.numer;
    }
}

// impl<T> Div for Fraction<T>
// where
//     T: Integer + Copy + NumAssign + Neg<Output = T> + Zero + One,
// {
//     type Output = Self;
//
//     fn div(self, other: Self) -> Self::Output {
//         let mut res = self;
//         res /= other;
//         res
//     }
// }

impl<T> SubAssign for Fraction<T>
where
    T: Integer + Copy + NumAssign + Neg<Output = T>,
{
    /// The function `sub_assign` subtracts another value from the current value and normalizes the
    /// result.
    ///
    /// Arguments:
    ///
    /// * `other`: The `other` parameter is of the same type as `self` and represents another instance
    ///            of the same struct or class.
    fn sub_assign(&mut self, other: Self) {
        if self.is_nan() || other.is_nan() {
            self.set_nan();
            return;
        }
        if self.is_infinite() && other.is_infinite() {
            self.set_nan();
            return;
        }
        if self.is_infinite() {
            return;
        }
        if other.is_infinite() {
            *self = -other;
            return;
        }

        if self.denom == other.denom {
            self.numer -= other.numer;
            self.reduce();
            return;
        }

        let mut rhs = other;
        mem::swap(&mut self.denom, &mut rhs.numer);
        let common_n = self.reduce();
        let mut common_d = rhs.reduce();
        mem::swap(&mut self.denom, &mut rhs.numer);
        self.numer = self.cross(&rhs);
        self.denom *= rhs.denom;
        mem::swap(&mut self.denom, &mut common_d);
        self.reduce();
        self.numer *= common_n;
        self.denom *= common_d;
        self.reduce();
    }
}

// impl<T> Sub for Fraction<T>
// where
//     T: Integer + Copy + NumAssign + Zero + One,
// {
//     type Output = Self;
//
//     fn sub(self, other: Self) -> Self::Output {
//         let mut res = self;
//         res -= other;
//         res
//     }
// }

impl<T> AddAssign for Fraction<T>
where
    T: Integer + Copy + NumAssign + Zero + One,
{
    /// The function `add_assign` adds two fractions together and assigns the result to the first
    /// fraction.
    ///
    /// Arguments:
    ///
    /// * `other`: The `other` parameter is of type `Self`, which means it is the same type as the
    ///            struct or object that the `add_assign` method belongs to.
    fn add_assign(&mut self, other: Self) {
        if self.is_nan() || other.is_nan() {
            self.set_nan();
            return;
        }
        if self.is_infinite() {
            return;
        }
        if other.is_infinite() {
            *self = other;
            return;
        }

        if self.denom == other.denom {
            self.numer += other.numer;
            self.reduce();
            return;
        }

        let mut rhs = other;
        mem::swap(&mut self.denom, &mut rhs.numer);
        let common_n = self.reduce();
        let mut common_d = rhs.reduce();
        mem::swap(&mut self.denom, &mut rhs.numer);
        self.numer = self.numer * rhs.denom + self.denom * rhs.numer;
        self.denom *= rhs.denom;
        mem::swap(&mut self.denom, &mut common_d);
        self.reduce();
        self.numer *= common_n;
        self.denom *= common_d;
        self.reduce();
    }
}

// impl<T> Add for Fraction<T>
// where
//     T: Integer + Copy + NumAssign + Zero + One,
// {
//     type Output = Self;
//
//     fn add(self, other: Self) -> Self::Output {
//         let mut res = self;
//         res += other;
//         res
//     }
// }

impl<T> MulAssign<T> for Fraction<T>
where
    T: Integer + Copy + NumAssign,
{
    /// The function performs a multiplication assignment operation on a mutable reference to a value.
    ///
    /// Arguments:
    ///
    /// * `other`: `other` is a generic parameter of type `T`.
    fn mul_assign(&mut self, other: T) {
        let mut rhs = other;
        mem::swap(&mut self.numer, &mut rhs);
        self.reduce();
        self.numer *= rhs;
    }
}

// impl<T> Mul<T> for Fraction<T>
// where
//     T: Integer + Copy + NumAssign + Zero + One,
// {
//     type Output = Self;
//
//     fn mul(self, other: T) -> Self::Output {
//         let mut res = self;
//         res *= other;
//         res
//     }
// }

impl<T> DivAssign<T> for Fraction<T>
where
    T: Integer + Copy + NumAssign + Neg<Output = T>,
{
    /// The function performs division assignment by swapping the denominator with the given value,
    /// normalizing the fraction, and multiplying the denominator by the swapped value.
    ///
    /// Arguments:
    ///
    /// * `other`: `other` is a generic parameter of type `T`.
    #[allow(clippy::suspicious_op_assign_impl)]
    fn div_assign(&mut self, other: T) {
        let mut rhs = other;
        mem::swap(&mut self.denom, &mut rhs);
        self.normalize();
        self.denom *= rhs;
    }
}

// impl<T> Div<T> for Fraction<T>
// where
//     T: Integer + Copy + NumAssign + Neg<Output = T> + Zero + One,
// {
//     type Output = Self;
//
//     fn div(self, other: T) -> Self::Output {
//         let mut res = self;
//         res /= other;
//         res
//     }
// }

impl<T> SubAssign<T> for Fraction<T>
where
    T: Integer + Copy + NumAssign,
{
    /// The function subtracts a value from a numerator and updates the fraction.
    ///
    /// Arguments:
    ///
    /// * `other`: `other` is a generic parameter `T` which represents the value being subtracted from
    ///            `self.numer`.
    fn sub_assign(&mut self, other: T) {
        if self.denom == One::one() {
            self.numer -= other;
            self.reduce();
            return;
        }

        let mut rhs = other;
        mem::swap(&mut self.denom, &mut rhs);
        let common_n = self.reduce();
        mem::swap(&mut self.denom, &mut rhs);
        self.numer -= self.denom * rhs;
        self.reduce();
        self.numer *= common_n;
    }
}

// impl<T> Sub<T> for Fraction<T>
// where
//     T: Integer + Copy + NumAssign + Zero + One,
// {
//     type Output = Self;
//
//     fn sub(self, other: T) -> Self::Output {
//         let mut res = self;
//         res -= other;
//         res
//     }
// }

impl<T> AddAssign<T> for Fraction<T>
where
    T: Integer + Copy + NumAssign + Zero + One,
{
    /// The function `add_assign` adds a value to a numerator and updates the fraction.
    ///
    /// Arguments:
    ///
    /// * `other`: `other` is a generic parameter `T` which represents the value being added to `self`.
    fn add_assign(&mut self, other: T) {
        if self.denom == One::one() {
            self.numer += other;
            self.reduce();
            return;
        }

        let mut rhs = other;
        mem::swap(&mut self.denom, &mut rhs);
        let common_n = self.reduce();
        mem::swap(&mut self.denom, &mut rhs);
        self.numer += self.denom * rhs;
        self.reduce();
        self.numer *= common_n;
    }
}

// impl<T> Add<T> for Fraction<T>
// where
//     T: Integer + Copy + NumAssign + Zero + One,
// {
//     type Output = Self;
//
//     fn add(self, other: T) -> Self::Output {
//         let mut res = self;
//         res += other;
//         res
//     }
// }

macro_rules! forward_op_assign {
    (impl $imp:ident, $method:ident) => {
        impl<'a, T> $imp<&'a Fraction<T>> for Fraction<T>
        where
            T: Integer + Copy + NumAssign + Neg<Output = T> + Zero + One,
        {
            #[inline]
            fn $method(&mut self, other: &Self) {
                self.$method(other.clone())
            }
        }

        impl<'a, T> $imp<&'a T> for Fraction<T>
        where
            T: Integer + Copy + NumAssign + Neg<Output = T> + Zero + One,
        {
            #[inline]
            fn $method(&mut self, other: &T) {
                self.$method(other.clone())
            }
        }
    };
}

macro_rules! forward_op_assign_signed {
    (impl $imp:ident, $method:ident) => {
        impl<'a, T> $imp<&'a Fraction<T>> for Fraction<T>
        where
            T: Integer + Copy + NumAssign + Neg<Output = T> + Zero + One + Signed,
        {
            #[inline]
            fn $method(&mut self, other: &Self) {
                self.$method(other.clone())
            }
        }

        impl<'a, T> $imp<&'a T> for Fraction<T>
        where
            T: Integer + Copy + NumAssign + Neg<Output = T> + Zero + One + Signed,
        {
            #[inline]
            fn $method(&mut self, other: &T) {
                self.$method(other.clone())
            }
        }
    };
}

forward_op_assign!(impl AddAssign, add_assign);
forward_op_assign!(impl SubAssign, sub_assign);
forward_op_assign_signed!(impl MulAssign, mul_assign);
forward_op_assign_signed!(impl DivAssign, div_assign);

macro_rules! forward_op {
    (impl $imp:ident, $method:ident, $op_assign:ident) => {
        impl<T> $imp for Fraction<T>
        where
            T: Integer + Copy + NumAssign + Neg<Output = T> + Zero + One,
        {
            type Output = Self;

            #[inline]
            fn $method(self, other: Self) -> Self::Output {
                let mut res = self;
                res.$op_assign(other);
                res
            }
        }

        impl<T> $imp<T> for Fraction<T>
        where
            T: Integer + Copy + NumAssign + Neg<Output = T> + Zero + One,
        {
            type Output = Self;

            #[inline]
            fn $method(self, other: T) -> Self::Output {
                let mut res = self;
                res.$op_assign(other);
                res
            }
        }
    };
}

macro_rules! forward_op_signed {
    (impl $imp:ident, $method:ident, $op_assign:ident) => {
        impl<T> $imp for Fraction<T>
        where
            T: Integer + Copy + NumAssign + Neg<Output = T> + Zero + One + Signed,
        {
            type Output = Self;

            #[inline]
            fn $method(self, other: Self) -> Self::Output {
                let mut res = self;
                res.$op_assign(other);
                res
            }
        }

        impl<T> $imp<T> for Fraction<T>
        where
            T: Integer + Copy + NumAssign + Neg<Output = T> + Zero + One + Signed,
        {
            type Output = Self;

            #[inline]
            fn $method(self, other: T) -> Self::Output {
                let mut res = self;
                res.$op_assign(other);
                res
            }
        }
    };
}

forward_op!(impl Add, add, add_assign);
forward_op!(impl Sub, sub, sub_assign);
forward_op_signed!(impl Mul, mul, mul_assign);
forward_op_signed!(impl Div, div, div_assign);

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
    fn test_const_abs() {
        assert_eq!(const_abs(-10), 10);
        assert_eq!(const_abs(10), 10);
        assert_eq!(const_abs(0), 0);
    }

    #[test]
    fn test_const_gcd() {
        assert_eq!(const_gcd(30, -40), 10);
        assert_eq!(const_gcd(30, 40), 10);
        assert_eq!(const_gcd(0, 5), 5);
        assert_eq!(const_gcd(5, 0), 5);
        assert_eq!(const_gcd(-30, -40), 10);
    }

    #[test]
    fn test_fraction_construction() {
        // Default construction
        let f: Fraction<i32> = Fraction::default();
        assert_eq!(f.numer(), &0);
        assert_eq!(f.denom(), &1);

        // From integer
        // let f = Fraction::from(5);
        let f = Fraction::new(5, 1);
        assert_eq!(f.numer(), &5);
        assert_eq!(f.denom(), &1);

        // New raw
        let f = Fraction::new_raw(3, 4);
        assert_eq!(f.numer(), &3);
        assert_eq!(f.denom(), &4);

        // New with normalization
        let f = Fraction::new(2, 4);
        assert_eq!(f.numer(), &1);
        assert_eq!(f.denom(), &2);

        // Negative denominator
        let f = Fraction::new(3, -4);
        assert_eq!(f.numer(), &-3);
        assert_eq!(f.denom(), &4);
    }

    #[test]
    fn test_fraction_normalization() {
        let mut f = Fraction::new_raw(4, 6);
        assert_eq!(f.reduce(), 2);
        assert_eq!(f.numer(), &2);
        assert_eq!(f.denom(), &3);

        let mut f = Fraction::new_raw(3, -4);
        f.keep_denom_positive();
        assert_eq!(f.numer(), &-3);
        assert_eq!(f.denom(), &4);

        let mut f = Fraction::new_raw(10, -5);
        f.normalize();
        assert_eq!(f.numer(), &-2);
        assert_eq!(f.denom(), &1);
    }

    #[test]
    fn test_fraction_arithmetic() {
        let f1 = Fraction::new(1, 2);
        let f2 = Fraction::new(1, 3);

        // Addition
        assert_eq!(f1 + f2, Fraction::new(5, 6));
        assert_eq!(f1 + 1, Fraction::new(3, 2));

        // Subtraction
        assert_eq!(f1 - f2, Fraction::new(1, 6));
        assert_eq!(f1 - 1, Fraction::new(-1, 2));

        // Multiplication
        assert_eq!(f1 * f2, Fraction::new(1, 6));
        assert_eq!(f1 * 2, Fraction::new(1, 1));

        // Division
        assert_eq!(f1 / f2, Fraction::new(3, 2));
        assert_eq!(f1 / 2, Fraction::new(1, 4));

        // Negation
        assert_eq!(-f1, Fraction::new(-1, 2));

        // Reciprocal
        assert_eq!(f1.inv(), Fraction::new(2, 1));
    }

    #[test]
    fn test_fraction_comparison() {
        let f1 = Fraction::new(1, 2);
        let f2 = Fraction::new(1, 3);
        let f3 = Fraction::new(2, 4);

        // Equality
        assert_eq!(f1, f3);
        assert_ne!(f1, f2);
        assert_eq!(Fraction::from(3), 3);
        assert_eq!(3, Fraction::from(3));

        // Ordering
        assert!(f1 > f2);
        assert!(f2 < f1);
        assert!(f1 >= f3);
        assert!(f1 <= f3);
        assert!(Fraction::new(3, 2) > 1);
        assert!(1 < Fraction::new(3, 2));
    }

    #[test]
    fn test_fraction_compound_assign() {
        let mut f = Fraction::new(1, 2);

        f += Fraction::new(1, 3);
        assert_eq!(f, Fraction::new(5, 6));

        f -= Fraction::new(1, 6);
        assert_eq!(f, Fraction::new(2, 3));

        f *= Fraction::new(3, 2);
        assert_eq!(f, Fraction::new(1, 1));

        f /= Fraction::new(2, 1);
        assert_eq!(f, Fraction::new(1, 2));

        f += 1;
        assert_eq!(f, Fraction::new(3, 2));

        f -= 1;
        assert_eq!(f, Fraction::new(1, 2));

        f *= 2;
        assert_eq!(f, Fraction::new(1, 1));

        f /= 2;
        assert_eq!(f, Fraction::new(1, 2));
    }

    #[test]
    fn test_fraction_special_values() {
        // let zero = Fraction::zero();
        let zero = Fraction::new(0, 1);
        assert!(zero.is_zero());
        assert!(!zero.is_infinite());
        assert!(!zero.is_nan());

        let mut f = Fraction::new(1, 1);
        f.set_zero();
        assert!(f.is_zero());

        let inf = Fraction::new_raw(1, 0);
        assert!(inf.is_infinite());
        assert!(!inf.is_nan());

        let nan = Fraction::new_raw(0, 0);
        assert!(nan.is_nan());
        assert!(!nan.is_infinite());
    }

    #[test]
    fn test_fraction_cross_product() {
        let f1 = Fraction::new(3, 4);
        let f2 = Fraction::new(-5, 6);
        assert_eq!(f1.cross(&f2), 38);
    }

    #[test]
    fn test_fraction_from_i32_to_i64() {
        let f: Fraction<i64> = Fraction::from(3_i32);
        assert_eq!(f, Fraction::new(3, 1));
    }

    #[test]
    fn test_fraction_abs() {
        let f = Fraction::new(-3, 4);
        assert_eq!(f.abs(), Fraction::new(3, 4));

        let f = Fraction::new(3, -4);
        assert_eq!(f.abs(), Fraction::new(3, 4));
    }

    #[test]
    fn test_fraction_increment_decrement() {
        let f = Fraction::new(3, 2);

        assert_eq!(f + 1, Fraction::new(5, 2));
        assert_eq!(f - 1, Fraction::new(1, 2));

        // assert_eq!(++f, Fraction::new(5, 2));
        // assert_eq!(f--, Fraction::new(5, 2));
        assert_eq!(f, Fraction::new(3, 2));
    }

    // #[test]
    // fn test_fraction_with_different_types() {
    //     let f_u32 = Fraction::new(1u32, 2u32);
    //     assert_eq!(f_u32.numer(), &1);
    //     assert_eq!(f_u32.denom(), &2);

    //     let f_i64 = Fraction::new(-1i64, 2i64);
    //     assert_eq!(f_i64.numer(), &-1);
    //     assert_eq!(f_i64.denom(), &2);
    // }
}
