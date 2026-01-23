use criterion::{black_box, criterion_group, criterion_main, Criterion};
use fractions::Fraction;
use num_traits::ops::inv::Inv;

fn bench_fraction_creation(c: &mut Criterion) {
    let mut group = c.benchmark_group("fraction_creation");

    group.bench_function("new_simple", |b| {
        b.iter(|| Fraction::new(black_box(3), black_box(4)));
    });

    group.bench_function("new_with_reduction", |b| {
        b.iter(|| Fraction::new(black_box(30), black_box(40)));
    });

    group.bench_function("new_negative_denom", |b| {
        b.iter(|| Fraction::new(black_box(3), black_box(-4)));
    });

    group.bench_function("new_large_numbers", |b| {
        b.iter(|| Fraction::new(black_box(123456789), black_box(987654321)));
    });

    group.finish();
}

fn bench_fraction_arithmetic(c: &mut Criterion) {
    let mut group = c.benchmark_group("arithmetic_operations");

    let f1 = Fraction::new(3, 4);
    let f2 = Fraction::new(5, 7);

    group.bench_function("addition", |b| {
        b.iter(|| black_box(f1) + black_box(f2));
    });

    group.bench_function("subtraction", |b| {
        b.iter(|| black_box(f1) - black_box(f2));
    });

    group.bench_function("multiplication", |b| {
        b.iter(|| black_box(f1) * black_box(f2));
    });

    group.bench_function("division", |b| {
        b.iter(|| black_box(f1) / black_box(f2));
    });

    group.finish();
}

fn bench_fraction_compound_assign(c: &mut Criterion) {
    let mut group = c.benchmark_group("compound_assign");

    let f1 = Fraction::new(3, 4);
    let f2 = Fraction::new(5, 7);

    group.bench_function("add_assign", |b| {
        let mut f = f1;
        b.iter(|| {
            f += black_box(f2);
            f = f1; // Reset
        });
    });

    group.bench_function("sub_assign", |b| {
        let mut f = f1;
        b.iter(|| {
            f -= black_box(f2);
            f = f1; // Reset
        });
    });

    group.bench_function("mul_assign", |b| {
        let mut f = f1;
        b.iter(|| {
            f *= black_box(f2);
            f = f1; // Reset
        });
    });

    group.bench_function("div_assign", |b| {
        let mut f = f1;
        b.iter(|| {
            f /= black_box(f2);
            f = f1; // Reset
        });
    });

    group.finish();
}

fn bench_fraction_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("comparison");

    let f1 = Fraction::new(3, 4);
    let f2 = Fraction::new(5, 7);
    let f3 = Fraction::new(6, 8);

    group.bench_function("equality", |b| {
        b.iter(|| black_box(f1) == black_box(f3));
    });

    group.bench_function("inequality", |b| {
        b.iter(|| black_box(f1) != black_box(f2));
    });

    group.bench_function("less_than", |b| {
        b.iter(|| black_box(f1) < black_box(f2));
    });

    group.bench_function("greater_than", |b| {
        b.iter(|| black_box(f1) > black_box(f2));
    });

    group.bench_function("cmp", |b| {
        b.iter(|| black_box(f1).cmp(black_box(&f2)));
    });

    group.finish();
}

fn bench_fraction_utilities(c: &mut Criterion) {
    let mut group = c.benchmark_group("utilities");

    let f = Fraction::new(-3, 4);

    group.bench_function("abs", |b| {
        b.iter(|| black_box(f).abs());
    });

    group.bench_function("neg", |b| {
        b.iter(|| -black_box(f));
    });

    group.bench_function("reciprocal", |b| {
        let mut frac = f;
        b.iter(|| {
            frac.reciprocal();
            frac = f; // Reset
        });
    });

    group.bench_function("inv", |b| {
        b.iter(|| black_box(f).inv());
    });

    group.bench_function("cross_product", |b| {
        let f1 = Fraction::new(3, 4);
        let f2 = Fraction::new(5, 7);
        b.iter(|| black_box(f1).cross(black_box(&f2)));
    });

    group.finish();
}

fn bench_fraction_normalization(c: &mut Criterion) {
    let mut group = c.benchmark_group("normalization");

    group.bench_function("normalize", |b| {
        let mut f = Fraction::new_raw(30, -40);
        b.iter(|| {
            f.normalize();
            f = Fraction::new_raw(30, -40); // Reset
        });
    });

    group.bench_function("reduce", |b| {
        let mut f = Fraction::new_raw(6, 8);
        b.iter(|| {
            f.reduce();
            f = Fraction::new_raw(6, 8); // Reset
        });
    });

    group.bench_function("keep_denom_positive", |b| {
        let mut f = Fraction::new_raw(3, -4);
        b.iter(|| {
            f.keep_denom_positive();
            f = Fraction::new_raw(3, -4); // Reset
        });
    });

    group.finish();
}

fn bench_fraction_i64(c: &mut Criterion) {
    let mut group = c.benchmark_group("i64_operations");

    let f1 = Fraction::<i64>::new(1234567890123456789, 987654321098765432);
    let f2 = Fraction::<i64>::new(1111111111111111111, 222222222222222222);

    group.bench_function("i64_addition", |b| {
        b.iter(|| black_box(f1) + black_box(f2));
    });

    group.bench_function("i64_multiplication", |b| {
        b.iter(|| black_box(f1) * black_box(f2));
    });

    group.bench_function("i64_comparison", |b| {
        b.iter(|| black_box(f1).cmp(black_box(&f2)));
    });

    group.finish();
}

fn bench_archimedes(c: &mut Criterion) {
    let mut group = c.benchmark_group("archimedes");

    let side_a = Fraction::<i32>::new(1, 2);
    let side_b = Fraction::<i32>::new(1, 4);
    let side_c = Fraction::<i32>::new(1, 6);

    group.bench_function("archimedes_i32", |b| {
        b.iter(|| {
            fractions::archimedes(black_box(&side_a), black_box(&side_b), black_box(&side_c))
        });
    });

    let side_a64 = Fraction::<i64>::new(1, 2);
    let side_b64 = Fraction::<i64>::new(1, 4);
    let side_c64 = Fraction::<i64>::new(1, 6);

    group.bench_function("archimedes_i64", |b| {
        b.iter(|| {
            fractions::archimedes(
                black_box(&side_a64),
                black_box(&side_b64),
                black_box(&side_c64),
            )
        });
    });

    group.finish();
}

fn bench_gcd(c: &mut Criterion) {
    let mut group = c.benchmark_group("gcd");

    group.bench_function("const_gcd", |b| {
        b.iter(|| fractions::const_gcd(black_box(30), black_box(40)));
    });

    group.bench_function("const_gcd_large", |b| {
        b.iter(|| fractions::const_gcd(black_box(123456789), black_box(987654321)));
    });

    group.finish();
}

fn bench_special_values(c: &mut Criterion) {
    let mut group = c.benchmark_group("special_values");

    group.bench_function("zero", |b| {
        b.iter(Fraction::<i32>::zero);
    });

    group.bench_function("one", |b| {
        b.iter(Fraction::<i32>::one);
    });

    group.bench_function("is_zero", |b| {
        let f = Fraction::<i32>::zero();
        b.iter(|| f.is_zero());
    });

    group.bench_function("is_one", |b| {
        let f = Fraction::<i32>::one();
        b.iter(|| f.is_one());
    });

    group.bench_function("is_infinite", |b| {
        let f = Fraction::new_raw(1, 0);
        b.iter(|| f.is_infinite());
    });

    group.bench_function("is_nan", |b| {
        let f = Fraction::new_raw(0, 0);
        b.iter(|| f.is_nan());
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_fraction_creation,
    bench_fraction_arithmetic,
    bench_fraction_compound_assign,
    bench_fraction_comparison,
    bench_fraction_utilities,
    bench_fraction_normalization,
    bench_fraction_i64,
    bench_archimedes,
    bench_gcd,
    bench_special_values
);
criterion_main!(benches);
