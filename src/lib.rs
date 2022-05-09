pub mod fractions;
pub use crate::fractions::Fraction;

#[cfg(test)]
mod tests {
    use crate::fractions::Fraction;
    use num::integer::gcd;

    #[test]
    fn it_works() {
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
}
