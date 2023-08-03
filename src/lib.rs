pub mod fractions;
pub use crate::fractions::Fraction;
pub use crate::fractions::{const_abs, const_gcd};

#[cfg(test)]
mod tests {
    use super::*;
    use num_integer::gcd;
    use quickcheck_macros::quickcheck;

    #[test]
    fn it_works() {
        const RESULT: i32 = const_gcd(4, -6);
        assert_eq!(RESULT, 2);

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
    fn check_eq(num: u32, den: u32) -> bool {
        let p = Fraction::new(num as i32, den as i32);
        p == p
    }

    #[quickcheck]
    fn check_neg(num: u32, den: u32) -> bool {
        let p = Fraction::new(num as i32, den as i32);
        p == -(-p)
    }

    #[quickcheck]
    fn check_reciprocal(num: i32) -> bool {
        let mut p = Fraction::new(num / 2, 10000);
        let q = p;
        p.reciprocal();
        p.reciprocal();
        p == q
    }

    #[quickcheck]
    fn check_default(num: u32, den: u32) -> bool {
        let p = Fraction::new(num as i32, den as i32);
        let zero = Fraction::<i32>::default();
        p == p + zero
    }

    // #[quickcheck]
    // fn check_order(d1: u32, d2: u32) -> bool {
    //     let p = Fraction::new(2000000000, d1 as i32);
    //     let q = Fraction::new(2000000000, d2 as i32);
    //     p <= q || p > q
    // }

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
}
