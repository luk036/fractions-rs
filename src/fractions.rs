#![allow(unused_imports)]
#![allow(dead_code)]

#[cfg(test)]
use core::hash;
// use core::iter::{Product, Sum};
use core::ops::{Add, Div, Mul, Neg, Rem, Sub};
use core::ops::{AddAssign, DivAssign, MulAssign, SubAssign};

// use core::str::FromStr;
use num::integer::gcd;
use num::Integer;
use num_traits::{Num, NumAssign, One, Zero};
// #[cfg(feature = "std")]
// use std::error::Error;
use std::cmp::Ordering;
use std::mem; // for swap

#[derive(PartialEq, Eq, Copy, Clone, Hash, Debug)]
pub struct Fraction<T: Integer> {
    /// numerator portion of the Fraction object
    num: T,
    /// denominator portion of the Fraction object
    den: T,
}

impl<T> Fraction<T>
where
    T: Integer + Zero + One + Neg<Output = T> + DivAssign + Copy,
{
    /**
    Create a new Fraction

    Examples:

    ```rust
    use fractions::Fraction;
    let f = Fraction::new(30, -40);

    assert_eq!(f, Fraction::new(-3, 4));
    ```
    */
    #[inline]
    pub fn new(num: T, den: T) -> Self {
        let mut res = Fraction { num, den };
        res.normalize();
        res
    }

    /**
     * @brief normalize to a canonical form
     *
     * denominator is always non-negative and co-prime with numerator
     */
    #[inline]
    pub fn normalize(&mut self) -> T {
        self.normalize1();
        self.normalize2()
    }
}

impl<T: Integer + Zero + One + DivAssign + Copy> Fraction<T> {
    /**
     * @brief normalize to a canonical form
     *
     * denominator is always co-prime with numerator
     */
    #[inline]
    pub fn normalize2(&mut self) -> T {
        let common = gcd(self.num, self.den);
        if common != One::one() && common != Zero::zero() {
            self.num /= common;
            self.den /= common;
        }
        common
    }
}

impl<T: Integer + Zero + Neg<Output = T> + Ord + Copy> Fraction<T> {
    /**
     * Normalize to a canonical form
     *
     * denominator is always non-negative
     */
    #[inline]
    pub fn normalize1(&mut self) {
        if self.den < Zero::zero() {
            self.num = -self.num;
            self.den = -self.den;
        }
    }

    /**
    Reciprocal

    Examples:

    ```rust
    use fractions::Fraction;
    let mut f = Fraction::new(30, -40);
    f.reciprocal();

    assert_eq!(f, Fraction::new(-4, 3));
    ```
    */
    #[inline]
    pub fn reciprocal(&mut self) {
        mem::swap(&mut self.num, &mut self.den);
        self.normalize1();
    }
}

impl<T: Integer + One> Fraction<T> {
    /**
    From an integer

    Examples:

    ```rust
    use fractions::Fraction;
    let mut f = Fraction::from(3);

    assert_eq!(f, Fraction::new(3, 1));
    ```
    */
    #[inline]
    pub fn from(num: T) -> Self {
        Fraction {
            num,
            den: One::one(),
        }
    }
}

impl<T: Integer + One + Zero> Default for Fraction<T> {
    /**
    Default Fraction

    Examples:

    ```rust
    use fractions::Fraction;
    let mut f = Fraction::<i32>::default();

    assert_eq!(f, Fraction::new(0, 1));
    ```
    */
    #[inline]
    fn default() -> Self {
        Fraction {
            num: Zero::zero(),
            den: One::one(),
        }
    }
}

impl<T: Integer + Copy> Fraction<T> {
    /**
     * @brief cross product
     */
    #[inline]
    pub fn cross(&self, rhs: &Self) -> T {
        self.num * rhs.den - self.den * rhs.num
    }
}

impl<T: Integer + Neg<Output = T>> Neg for Fraction<T> {
    type Output = Fraction<T>;

    /**
    Negation

    Examples:

    ```rust
    use fractions::Fraction;
    let mut f = Fraction::new(3, 4);

    assert_eq!(-f, Fraction::new(-3, 4));
    ```
    */
    #[inline]
    fn neg(self) -> Self::Output {
        let mut res = self;
        res.num = -res.num;
        res
    }
}

impl<T: Integer + PartialEq + Copy + DivAssign> PartialEq<T> for Fraction<T> {
    /**
    Equal to

    Examples:

    ```rust
    use fractions::Fraction;
    let f = Fraction::from(3);
    let g = Fraction::new(3, 4);

    assert!(f == 3);
    assert!(g != 3);
    ```
    */
    #[inline]
    fn eq(&self, other: &T) -> bool {
        self.den == One::one() && self.num == *other
    }
}
// impl<T: Num + Eq + Clone> Eq for Fraction<T> {}

impl<T: Integer + PartialOrd + Copy + DivAssign> PartialOrd<T> for Fraction<T> {
    /**
    PartialOrd

    Examples:

    ```rust
    use fractions::Fraction;
    let f = Fraction::new(3, 4);

    assert!(f < 1);
    assert!(f > 0);
    ```
    */
    fn partial_cmp(&self, other: &T) -> Option<Ordering> {
        if self.den == One::one() || *other == Zero::zero() {
            return self.num.partial_cmp(other);
        }
        let mut lhs = Self {
            num: self.num.clone(),
            den: other.clone(),
        };
        let rhs = self.den.clone();
        lhs.normalize2();
        lhs.num.partial_cmp(&(lhs.den * rhs))
    }
}

macro_rules! scalar_ord_eq {
    ($($scalar:ident),*) => (
        $(
            impl PartialEq<Fraction<$scalar>> for $scalar {
                #[inline]
                fn eq(&self, other: &Fraction<$scalar>) -> bool {
                    other.den == 1 as $scalar && other.num == *self
                }
            }

            impl PartialOrd<Fraction<$scalar>> for $scalar {
                fn partial_cmp(&self, other: &Fraction<$scalar>) -> Option<Ordering> {
                    if other.den == 1 as $scalar || *self == 0 as $scalar {
                        return self.partial_cmp(&other.num);
                    }
                    let mut rhs = Fraction {
                        num: other.num.clone(),
                        den: self.clone(),
                    };
                    let lhs = other.den.clone();
                    rhs.normalize();
                    (lhs * rhs.den).partial_cmp(&rhs.num)
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
    /**
    PartialOrd

    Examples:

    ```rust
    use fractions::Fraction;
    let f = Fraction::new(3, 4);
    let g = Fraction::new(5, 7);

    assert!(f > g);
    ```
    */
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        if self.den == other.den {
            return self.num.cmp(&other.num);
        }
        let mut lhs = Self {
            num: self.num.clone(),
            den: other.num.clone(),
        };
        let mut rhs = Self {
            num: self.den.clone(),
            den: other.den.clone(),
        };
        lhs.normalize2();
        rhs.normalize2();
        (lhs.num * rhs.den).cmp(&(lhs.den * rhs.num))
    }
}

// Op Assign

impl<T> MulAssign for Fraction<T>
where
    T: Integer + Copy + NumAssign + Zero + One,
{
    fn mul_assign(&mut self, other: Self) {
        let mut rhs = other;
        mem::swap(&mut self.num, &mut rhs.num);
        self.normalize2();
        rhs.normalize2();
        self.num *= rhs.num;
        self.den *= rhs.den;
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
    T: Integer + Copy + NumAssign + Neg<Output = T> + Zero + One,
{
    fn div_assign(&mut self, other: Self) {
        let mut rhs = other;
        mem::swap(&mut self.den, &mut rhs.num);
        self.normalize();
        rhs.normalize2();
        self.num *= rhs.den;
        self.den *= rhs.num;
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
    T: Integer + Copy + NumAssign + Zero + One,
{
    fn sub_assign(&mut self, other: Self) {
        if self.den == other.den {
            self.num -= other.num;
            self.normalize2();
            return;
        }

        let mut rhs = other;
        mem::swap(&mut self.den, &mut rhs.num);
        let common_n = self.normalize2();
        let mut common_d = rhs.normalize2();
        mem::swap(&mut self.den, &mut rhs.num);
        self.num = self.cross(&rhs);
        self.den *= rhs.den;
        mem::swap(&mut self.den, &mut common_d);
        self.normalize2();
        self.num *= common_n;
        self.den *= common_d;
        self.normalize2();
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
    fn add_assign(&mut self, other: Self) {
        if self.den == other.den {
            self.num += other.num;
            self.normalize2();
            return;
        }

        let mut rhs = other;
        mem::swap(&mut self.den, &mut rhs.num);
        let common_n = self.normalize2();
        let mut common_d = rhs.normalize2();
        mem::swap(&mut self.den, &mut rhs.num);
        self.num = self.num * rhs.den + self.den * rhs.num;
        self.den *= rhs.den;
        mem::swap(&mut self.den, &mut common_d);
        self.normalize2();
        self.num *= common_n;
        self.den *= common_d;
        self.normalize2();
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
    T: Integer + Copy + NumAssign + Zero + One,
{
    fn mul_assign(&mut self, other: T) {
        let mut rhs = other;
        mem::swap(&mut self.num, &mut rhs);
        self.normalize2();
        self.num *= rhs;
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
    T: Integer + Copy + NumAssign + Neg<Output = T> + Zero + One,
{
    fn div_assign(&mut self, other: T) {
        let mut rhs = other;
        mem::swap(&mut self.den, &mut rhs);
        self.normalize();
        self.den *= rhs;
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
    T: Integer + Copy + NumAssign + Zero + One,
{
    fn sub_assign(&mut self, other: T) {
        if self.den == One::one() {
            self.num -= other;
            self.normalize2();
            return;
        }

        let mut rhs = other;
        mem::swap(&mut self.den, &mut rhs);
        let common_n = self.normalize2();
        mem::swap(&mut self.den, &mut rhs);
        self.num -= self.den * rhs;
        self.normalize2();
        self.num *= common_n;
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
    fn add_assign(&mut self, other: T) {
        if self.den == One::one() {
            self.num += other;
            self.normalize2();
            return;
        }

        let mut rhs = other;
        mem::swap(&mut self.den, &mut rhs);
        let common_n = self.normalize2();
        mem::swap(&mut self.den, &mut rhs);
        self.num += self.den * rhs;
        self.normalize2();
        self.num *= common_n;
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

forward_op_assign!(impl AddAssign, add_assign);
forward_op_assign!(impl SubAssign, sub_assign);
forward_op_assign!(impl MulAssign, mul_assign);
forward_op_assign!(impl DivAssign, div_assign);

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

forward_op!(impl Add, add, add_assign);
forward_op!(impl Sub, sub, sub_assign);
forward_op!(impl Mul, mul, mul_assign);
forward_op!(impl Div, div, div_assign);

// /**
//  * @brief multiply
//  *
//  * @param lhs
//  * @param rhs
//  * @return Fraction
//  */
// pub fn operator*(Fraction lhs, const Fraction& rhs) -> Fraction {
//     return lhs *= rhs;
// }
//
// /**
//  * @brief multiply
//  *
//  * @param lhs
//  * @param rhs
//  * @return Fraction
//  */
// pub fn operator*(Fraction lhs, const T& rhs) -> Fraction {
//     return lhs *= rhs;
// }
//
// /**
//  * @brief multiply
//  *
//  * @param lhs
//  * @param rhs
//  * @return Fraction
//  */
// pub fn operator*(const T& lhs, Fraction rhs) -> Fraction {
//     return rhs *= lhs;
// }
//
// /**
//  * @brief divide
//  *
//  * @param lhs
//  * @param rhs
//  * @return Fraction
//  */
// pub fn operator/(Fraction lhs, const Fraction& rhs) -> Fraction {
//     return lhs /= rhs;
// }
//
// /**
//  * @brief divide
//  *
//  * @param lhs
//  * @param rhs
//  * @return Fraction
//  */
// pub fn operator/(Fraction lhs, const T& rhs) -> Fraction {
//     return lhs /= rhs;
// }
//
// /**
//  * @brief divide
//  *
//  * @param lhs
//  * @param rhs
//  * @return Fraction
//  */
// pub fn operator/(const T& lhs, Fraction rhs) -> Fraction {
//     rhs.reciprocal();
//     return rhs *= lhs;
// }
//
// /**
//  * @brief Add
//  *
//  * @param rhs
//  * @return Fraction
//  */
// pub fn operator+(const Fraction& rhs) const -> Fraction {
//     if self.den == rhs.den {
//         return Fraction(self.num + rhs.num, self.den);
//     }
//     let common = gcd(self.den, rhs.den);
//     if common == Zero::zero() {
//         return Fraction(rhs.den * self.num + self.den * rhs.num, Zero::zero());
//     }
//     let l = self.den / common;
//     let r = rhs.den / common;
//     let mut d = self.den * r;
//     let mut n = r * self.num + l * rhs.num;
//     return Fraction(std::move(n), std::move(d));
// }
//
// /**
//  * @brief Subtract
//  *
//  * @param[in] frac
//  * @return Fraction
//  */
// pub fn operator-(const Fraction& frac) const -> Fraction { return *this + (-frac); }
//
// /**
//  * @brief Add
//  *
//  * @param[in] frac
//  * @param[in] i
//  * @return Fraction
//  */
// pub fn operator+(Fraction frac, const T& i) -> Fraction { return frac += i; }
//
// /**
//  * @brief Add
//  *
//  * @param[in] i
//  * @param[in] frac
//  * @return Fraction
//  */
// pub fn operator+(const T& i, Fraction frac) -> Fraction { return frac += i; }
//
// /**
//  * @brief
//  *
//  * @param[in] i
//  * @return Fraction
//  */
// pub fn operator-(const T& i) const -> Fraction { return *this + (-i); }
//
// /**
//  * @brief
//  *
//  * @param[in] rhs
//  * @return Fraction
//  */
// pub fn operator+=(const Fraction& rhs) -> Fraction& { return *this -= (-rhs); }
//
// /**
//  * @brief
//  *
//  * @param[in] rhs
//  * @return Fraction
//  */
// pub fn operator-=(const Fraction& rhs) -> Fraction& {
//     if self.den == rhs.den {
//         self.num -= rhs.num;
//         self.normalize2();
//         return *this;
//     }
//
//     let mut other{rhs};
//     mem::swap(&mut self.den, &mut other.num);
//     let mut common_n = self.normalize2();
//     let mut common_d = other.normalize2();
//     mem::swap(&mut self.den, &mut other.num);
//     self.num = self.cross(other);
//     self.den *= other.den;
//     mem::swap(&mut self.den, &mut common_d);
//     self.normalize2();
//     self.num *= common_n;
//     self.den *= common_d;
//     self.normalize2();
//     return *this;
// }
//
// /**
//  * @brief
//  *
//  * @param[in] i
//  * @return Fraction
//  */
// pub fn operator+=(const T& i) -> Fraction& { return *this -= (-i); }
//
// /**
//  * @brief
//  *
//  * @param[in] rhs
//  * @return Fraction
//  */
// pub fn operator-=(const T& rhs) -> Fraction& {
//     if self.den == One::one() {
//         self.num -= rhs;
//         return *this;
//     }
//
//     let mut other{rhs};
//     mem::swap(&mut self.den, &mut other);
//     let mut common_n = self.normalize2();
//     mem::swap(&mut self.den, &mut other);
//     self.num -= other * self.den;
//     self.num *= common_n;
//     self.normalize2();
//     return *this;
// }
//
// /**
//  * @brief
//  *
//  * @param[in] c
//  * @param[in] frac
//  * @return Fraction
//  */
// pub fn operator-(const T& c, const Fraction& frac) -> Fraction {
//     return c + (-frac);
// }
//
// /**
//  * @brief
//  *
//  * @param[in] c
//  * @param[in] frac
//  * @return Fraction
//  */
// pub fn operator+(int&& c, const Fraction& frac) -> Fraction {
//     return frac + T(c);
// }
//
// /**
//  * @brief
//  *
//  * @param[in] c
//  * @param[in] frac
//  * @return Fraction
//  */
// pub fn operator-(int&& c, const Fraction& frac) -> Fraction {
//     return (-frac) + T(c);
// }
//
// /**
//  * @brief
//  *
//  * @param[in] c
//  * @param[in] frac
//  * @return Fraction<T>
//  */
// pub fn operator*(int&& c, const Fraction& frac) -> Fraction {
//     return frac * T(c);
// }
//
// /**
//  * @brief
//  *
//  * @tparam _Stream
//  * @tparam T
//  * @param[in] os
//  * @param[in] frac
//  * @return _Stream&
//  */
// template <typename _Stream> pub fn operator<<(_Stream& os, const Fraction& frac)
//     -> _Stream& {
//     os << "(" << frac.num() << "/" << frac.den() << ")";
//     return os;
// }

// For template deduction
// Integral{T} Fraction(const T &, const T &) noexcept -> Fraction<T>;
