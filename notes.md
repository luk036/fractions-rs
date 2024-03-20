Sure, here's an example of a generic Fraction class in Rust that accepts different negative integer types, along with a corresponding test module:

Fraction.rs
```rust
use std::num::One;

struct Fraction<T> {
    num: T,
    den: T,
}

impl<T> Fraction<T> {
    fn new(num: T, den: T) -> Self {
        Self { num, den }
    }

    fn reduce(&self) -> Self {
        let gcd = self.greatest_common_divisor();
        Self {
            num: self.num / gcd,
            den: self.den / gcd,
        }
    }

    fn greatest_common_divisor(&self) -> T {
        self.num.gcd(self.den)
    }

    fn add(&self, other: &Fraction<T>) -> Self {
        Self {
            num: self.num * other.den + other.num * self.den,
            den: self.den * other.den,
        }
    }

    fn sub(&self, other: &Fraction<T>) -> Self {
        Self {
            num: self.num * other.den - other.num * self.den,
            den: self.den * other.den,
        }
    }

    fn mul(&self, other: &Fraction<T>) -> Self {
        Self {
            num: self.num * other.num,
            den: self.den * other.den,
        }
    }

    fn div(&self, other: &Fraction<T>) -> Self {
        Self {
            num: self.num * other.den,
            den: self.den * other.num,
        }
    }
}
```

FractionTest.rs
```
use std::testing::{assert_eq};
use Fraction;

#[test]
fn test_fraction_construction() {
    let f = Fraction::<i32>::new(1, 2);
    assert_eq!(f.num, 1);
    assert_eq!(f.den, 2);
}

#[test]
fn test_fraction_reduction() {
    let f = Fraction::<i32>::new(4, 8);
    assert_eq!(f.reduce(), Fraction::<i32>::new(1, 2));
}

#[test]
fn test_fraction_addition() {
    let f1 = Fraction::<i32>::new(1, 2);
    let f2 = Fraction::<i32>::new(3, 4);
    assert_eq!(f1.add(&f2), Fraction::<i32>::new(7, 8));
}

#[test]
fn test_fraction_subtraction() {
    let f1 = Fraction::<i32>::new(1, 2);
    let f2 = Fraction::<i32>::new(3, 4);
    assert_eq!(f1.sub(&f2), Fraction::<i32>::new(-1, 2));
}

#[test]
fn test_fraction_multiplication() {
    let f1 = Fraction::<i32>::new(1, 2);
    let f2 = Fraction::<i32>::new(3, 4);
    assert_eq!(f1.mul(&f2), Fraction::<i32>::new(3, 8));
}

#[test]
fn test_fraction_division() {
    let f1 = Fraction::<i32>::new(1, 2);
    let f2 = Fraction::<i32>::new(3, 4);
    assert_eq!(f1.div(&f2), Fraction::<i32>::new(2, 3));
}

#[test]
fn test_fraction_negative_numbers() {
    let f1 = Fraction::<i32>::new(-1, 2);
    let f2 = Fraction::<i32>::new(3, 4);
    assert_eq!(f1.add(&f2), Fraction::<i32>::new(-1, 2));
}
```
In this implementation, we've made the `Fraction` struct generic over an integer type `T`. We've also updated the `Fraction::new` method to take two parameters of type `T` and `T` respectively. Additionally, we've updated the `greatest_common_divisor` method to return a `T` value.

In the test module, we've written six test cases that exercise the different methods of the `Fraction` struct, just like in the previous example. However, this time we've used the `i32` type to create the fractions.

Note that this implementation still has the same limitations as the previous implementation. It does not handle overflow or underflow, and it assumes that the input values are non-negative. Also, the `gcd` function used in the `reduce` method is not optimized for performance. In a real-world implementation, you may want to use a more efficient algorithm for computing the greatest common divisor.

Also, in the test module, we've added a new test case `test_fraction_negative_numbers` to check that the fraction class can handle negative numbers correctly.

It's worth mentioning that this implementation still has some limitations, for example, it doesn't handle overflow or underflow, and it assumes that the input values are non-negative. Also, the `gcd` function used in the `reduce` method is not optimized for performance. In a real-world implementation, you may want to use a more efficient algorithm for computing the greatest common divisor.
