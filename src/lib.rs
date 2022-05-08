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

        let f = Fraction::new(30, 40);
        assert_eq!(f.num, 3);
        assert_eq!(f.den, 4);

        let h = Fraction::from(30);
        assert_eq!(h.num, 30);
        assert_eq!(h.den, 1);

        let g = Fraction::<i32>::default();
        assert_eq!(g.num, 0);
        assert_eq!(g.den, 1);

        // assert_eq!(result, 30);
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
        let f = Fraction::new(30, 40);
        assert!(f != 1i32);
        assert!(1i32 != f);
        assert!(f < 1i32);
        // assert!(1i32 > f);
        // assert_eq!(result, 30);
    }
}
