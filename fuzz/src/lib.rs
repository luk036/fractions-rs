// Fuzz testing targets for fractions-rs
#![no_main]

use fractions::Fraction;
use libfuzzer_sys::fuzz_target;

// Fuzz the Fraction::new function with valid inputs
fuzz_target!(|data: (i64, i64)| {
    let (numer, denom) = data;
    // Only test with non-zero denominator to avoid special values
    if denom != 0 {
        let _ = Fraction::<i64>::new(numer, denom);
    }
});

// Fuzz addition
fuzz_target!(|data: (i64, i64, i64, i64)| {
    let (a_num, a_den, b_num, b_den) = data;
    if a_den != 0 && b_den != 0 {
        let a = Fraction::<i64>::new(a_num, a_den);
        let b = Fraction::<i64>::new(b_num, b_den);
        let _ = a + b;
    }
});

// Fuzz multiplication
fuzz_target!(|data: (i64, i64, i64, i64)| {
    let (a_num, a_den, b_num, b_den) = data;
    if a_den != 0 && b_den != 0 {
        let a = Fraction::<i64>::new(a_num, a_den);
        let b = Fraction::<i64>::new(b_num, b_den);
        let _ = a * b;
    }
});

// Fuzz division
fuzz_target!(|data: (i64, i64, i64, i64)| {
    let (a_num, a_den, b_num, b_den) = data;
    if a_den != 0 && b_den != 0 && !(b_num == 0 && b_den == 0) {
        let a = Fraction::<i64>::new(a_num, a_den);
        let b = Fraction::<i64>::new(b_num, b_den);
        let _ = a / b;
    }
});

// Fuzz string parsing
fuzz_target!(|data: &[u8]| {
    if let Ok(s) = core::str::from_utf8(data) {
        let _ = s.parse::<Fraction<i64>>();
    }
});
