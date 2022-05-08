#![allow(unused_imports)]
#![allow(dead_code)]

#[cfg(test)]
use core::hash;
// use core::iter::{Product, Sum};
use core::ops::{Add, Div, Mul, Neg, Rem, Sub};
use core::ops::{AddAssign, DivAssign, MulAssign};

// use core::str::FromStr;
use num::integer::gcd;
use num::Integer;
use num_traits::{Num, One, Zero};
// #[cfg(feature = "std")]
// use std::error::Error;
use std::cmp::Ordering;
use std::mem; // for swap

#[derive(PartialEq, Eq, Copy, Clone, Hash, Debug)]
pub struct Fraction<T: Integer> {
    /// numerator portion of the Fraction object
    pub num: T,
    /// denominator portion of the Fraction object
    pub den: T,
}

impl<T: Integer + Zero + One + Neg<Output = T> + DivAssign + Copy> Fraction<T> {
    /**
    Create a new Fraction

    Examples:

    ```rust
    use fractions::Fraction;
    let f = Fraction::new(30, 40);

    assert_eq!(f.num, 3);
    assert_eq!(f.den, 4);
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
    let mut f = Fraction::new(30, 40);
    f.reciprocal();

    assert_eq!(f.num, 4);
    assert_eq!(f.den, 3);
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

    assert_eq!(f.num, 3);
    assert_eq!(f.den, 1);
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

    assert_eq!(f.num, 0);
    assert_eq!(f.den, 1);
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

impl<T: Integer + PartialEq + Copy + DivAssign> PartialEq<T> for Fraction<T> {
    /**
    @brief Equal to

    Examples:

    ```rust
    use fractions::Fraction;
    let mut f = Fraction::from(3);

    assert_eq!(f, 3);
    ```
     */
    #[inline]
    fn eq(&self, other: &T) -> bool {
        self.den == One::one() && self.num == *other
    }
}
// impl<T: Num + Eq + Clone> Eq for Fraction<T> {}

macro_rules! scalar_eq {
    ($($scalar:ident),*) => (
        $(
            impl PartialEq<Fraction<$scalar>> for $scalar {
                #[inline]
                fn eq(&self, other: &Fraction<$scalar>) -> bool {
                    other.den == 1 as $scalar && other.num == *self
                }
            }
        )*
    );
}

scalar_eq!(i32, i64, usize, u32, u64);

// impl PartialEq<Fraction<i32>> for i32 {
//     /**
//     @brief Equal to
//
//     Examples:
//
//     ```rust
//     use fractions::Fraction;
//     let mut f = Fraction::from(3);
//
//     assert!(3 == f);
//     ```
//      */
//     #[inline]
//     fn eq(&self, other: &Fraction<i32>) -> bool {
//         other.den == 1 && other.num == *self
//     }
// }
// impl<T: Num + Eq + Clone> Eq for Fraction<T> {}

impl<T: Integer + PartialOrd + Copy + DivAssign> PartialOrd<T> for Fraction<T> {
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

// impl<T: Integer + PartialOrd + Copy + DivAssign> PartialOrd<Fraction<T>> for T {
//     fn partial_cmp(&self, other: &Fraction<T>) -> Option<Ordering> {
//         if *self == Zero::zero() || other.den == One::one() {
//             return self.partial_cmp(&other.num);
//         }
//         let lhs = other.den.clone();
//         let mut rhs = Self { num: other.num.clone(), den: self.clone() };
//         rhs.normalize2();
//         (rhs.den * lhs).partial_cmp(&rhs.num)
//     }
// }

// impl PartialOrd<Fraction<i32>> for i32 {
//     fn partial_cmp(&self, other: &Fraction<i32>) -> Option<Ordering> {
//         if *self == Zero::zero() || other.den == One::one() {
//             return self.partial_cmp(&other.num);
//         }
//         let lhs = other.den.clone();
//         let mut rhs = Self { num: other.num.clone(), den: self.clone() };
//         rhs.normalize2();
//         (rhs.den * lhs).partial_cmp(&rhs.num)
//     }
// }

// impl<T: Integer + PartialEq + Copy + DivAssign> PartialEq for Fraction<T> {
//     fn eq(&self, other: &Self) -> bool {
//         if self.den == other.den {
//             return self.num == other.num;
//         }
//         let mut lhs = Self { num: self.num.clone(), den: other.num.clone() };
//         let mut rhs = Self { num: other.den.clone(), den: self.den.clone() };
//         lhs.normalize2();
//         rhs.normalize2();
//         lhs.num * rhs.den == lhs.den * rhs.num
//     }
// }
// impl<T: Integer + Eq + Copy + DivAssign> Eq for Fraction<T> {}

impl<T: Integer + PartialOrd + Copy + DivAssign> PartialOrd for Fraction<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: Integer + Ord + Copy + DivAssign> Ord for Fraction<T> {
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
            num: other.den.clone(),
            den: self.den.clone(),
        };
        lhs.normalize2();
        rhs.normalize2();
        (lhs.num * rhs.den).cmp(&(lhs.den * rhs.num))
    }
}

// Op Assign

mod opassign {
    use crate::fractions::Fraction;
    use core::ops::{Add, Div, Mul, Neg, Rem, Sub};
    use core::ops::{AddAssign, DivAssign, MulAssign, SubAssign};
    use num::Integer;
    use num_traits::{Num, NumAssign, One, Zero};
    use std::mem;

    impl<T: Integer + Copy + NumAssign + Zero + One> MulAssign for Fraction<T> {
        fn mul_assign(&mut self, other: Self) {
            let mut rhs = other;
            mem::swap(&mut self.num, &mut rhs.num);
            self.normalize2();
            rhs.normalize2();
            self.num *= rhs.num;
            self.den *= rhs.den;
        }
    }

    impl<T: Integer + Copy + NumAssign + Neg<Output = T> + Zero + One> DivAssign for Fraction<T> {
        fn div_assign(&mut self, other: Self) {
            let mut rhs = other;
            mem::swap(&mut self.den, &mut rhs.num);
            self.normalize();
            rhs.normalize2();
            self.num *= rhs.den;
            self.den *= rhs.num;
        }
    }

    // impl<T: Integer + Clone + NumAssign> AddAssign for Fraction<T> {
    //     fn add_assign(&mut self, other: Self) {
    //         self.num += other.num;
    //         self.den += other.den;
    //     }
    // }
    //
    // impl<T: Integer + Clone + NumAssign> SubAssign for Fraction<T> {
    //     fn sub_assign(&mut self, other: Self) {
    //         self.num -= other.num;
    //         self.den -= other.den;
    //     }
    // }

    macro_rules! forward_op_assign1 {
        (impl $imp:ident, $method:ident) => {
            impl<'a, T: Integer + Copy + NumAssign + Neg<Output = T> + Zero + One>
                $imp<&'a Fraction<T>> for Fraction<T>
            {
                #[inline]
                fn $method(&mut self, other: &Self) {
                    self.$method(other.clone())
                }
            }
        };
    }

    macro_rules! forward_op_assign2 {
        (impl $imp:ident, $method:ident) => {
            impl<'a, T: Integer + Copy + NumAssign + Neg<Output = T> + Zero + One> $imp<&'a T>
                for Fraction<T>
            {
                #[inline]
                fn $method(&mut self, other: &T) {
                    self.$method(other.clone())
                }
            }
        };
    }

    // forward_op_assign1!(impl AddAssign, add_assign);
    // forward_op_assign1!(impl SubAssign, sub_assign);
    forward_op_assign1!(impl MulAssign, mul_assign);
    forward_op_assign1!(impl DivAssign, div_assign);
}

// /**
//  * @brief multiply and assign
//  *
//  * @param rhs
//  * @return Fraction&
//  */
// pub fn operator*=(Fraction rhs) -> Fraction& {
//     mem::swap(&mut self.num, &mut rhs.num);
//     self.normalize2();
//     rhs.normalize2();
//     self.num *= rhs.num;
//     self.den *= rhs.den;
//     return *this;
// }
//
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
//  * @brief multiply and assign
//  *
//  * @param rhs
//  * @return Fraction&
//  */
// pub fn operator*=(T rhs) -> Fraction& {
//     mem::swap(&mut self.num, &mut rhs);
//     self.normalize2();
//     self.num *= rhs;
//     return *this;
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
//  * @brief divide and assign
//  *
//  * @param rhs
//  * @return Fraction&
//  */
// pub fn operator/=(Fraction rhs) -> Fraction& {
//     mem::swap(&mut self.den, &mut rhs.num);
//     self.normalize();
//     rhs.normalize2();
//     self.num *= rhs.den;
//     self.den *= rhs.num;
//     return *this;
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
//  * @brief divide and assign
//  *
//  * @param rhs
//  * @return Fraction&
//  */
// pub fn operator/=(const T& rhs) -> Fraction& {
//     mem::swap(&mut self.den, &mut rhs);
//     self.normalize();
//     self.den *= rhs;
//     return *this;
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
//  * @brief Negate
//  *
//  * @return Fraction
//  */
// pub fn operator-() const -> Fraction {
//     let mut res = Fraction(*this);
//     res.num = -res.num;
//     return res;
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
