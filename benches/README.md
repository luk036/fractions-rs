# Benchmark Tests

This directory contains benchmark tests for the fractions-rs library using the Criterion benchmarking framework.

## Running Benchmarks

To run all benchmarks:
```bash
cargo bench
```

To run a specific benchmark group:
```bash
cargo bench bench_fraction_creation
cargo bench bench_fraction_arithmetic
cargo bench bench_fraction_comparison
```

To run benchmarks without executing them (just check compilation):
```bash
cargo bench --no-run
```

## Benchmark Groups

### `fraction_creation`
- Tests the performance of creating new Fraction instances
- Includes: simple creation, creation with reduction, negative denominators, large numbers

### `arithmetic_operations`
- Tests basic arithmetic operations
- Includes: addition, subtraction, multiplication, division

### `compound_assign`
- Tests compound assignment operators
- Includes: +=, -=, *=, /=

### `comparison`
- Tests comparison operations
- Includes: equality, inequality, less than, greater than, cmp

### `utilities`
- Tests utility functions
- Includes: abs, neg, reciprocal, inv, cross_product

### `normalization`
- Tests normalization operations
- Includes: normalize, reduce, keep_denom_positive

### `i64_operations`
- Tests operations with i64 integers
- Includes: addition, multiplication, comparison with large numbers

### `archimedes`
- Tests the archimedes function for triangle area calculation
- Includes: i32 and i64 variants

### `gcd`
- Tests GCD calculation performance
- Includes: const_gcd with small and large numbers

### `special_values`
- Tests special value operations
- Includes: zero, one, is_zero, is_one, is_infinite, is_nan

## Benchmark Results

After running benchmarks, results are saved in the `target/criterion/` directory. You can view HTML reports by opening `target/criterion/report/index.html` in a web browser.

## Performance Monitoring

These benchmarks can be used to monitor performance changes across different commits. Criterion automatically compares results with previous runs and highlights regressions or improvements.

## Adding New Benchmarks

To add a new benchmark:

1. Add a new function following the pattern:
```rust
fn bench_my_operation(c: &mut Criterion) {
    let mut group = c.benchmark_group("my_group");
    group.bench_function("my_benchmark", |b| {
        b.iter(|| {
            // Your benchmark code here
        });
    });
    group.finish();
}
```

2. Add the function to the `criterion_group!` macro:
```rust
criterion_group!(
    benches,
    bench_my_operation,
    // ... other benchmarks
);
```