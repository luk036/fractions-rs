# iFlow Context for fractions-rs

## Project Overview
The `fractions-rs` is a Rust library that provides an implementation of rational numbers (fractions) with support for basic arithmetic operations, comparisons, and special value handling (zero, infinity, NaN). The library is designed to work with generic integer types and includes implementations for common mathematical operations.

## Key Features
- Generic `Fraction<T>` struct for representing rational numbers
- Basic arithmetic operations: addition, subtraction, multiplication, division
- Support for compound assignment operators
- Comparison operations and equality testing
- Support for special values: zero, infinity, NaN
- Cross product calculation for comparing fractions without floating point errors
- Normalization of fractions to their canonical form
- Conversion from integers to fractions
- Absolute value and negation operations

## Project Structure
- `Cargo.toml` - Project manifest with dependencies and features
- `README.md` - Basic project information and installation instructions
- `src/lib.rs` - Library entry point, exports the main Fraction type and utility functions
- `src/fractions.rs` - Main implementation of the Fraction struct and its methods
- `src/main.rs` - A simple "Hello, World!" binary (not part of the library)
- `src/more_tests.rs` - Additional test cases
- `fractions.js` - JavaScript port/translation of the Rust implementation (appears to be a reference implementation)
- `.github/workflows/ci.yml` - CI configuration for testing, formatting, and documentation

## Core Implementation Details
- The `Fraction` struct consists of a numerator (`numer`) and denominator (`denom`) of type `T`
- Fractions are automatically normalized to their canonical form (lowest terms)
- The denominator is always kept positive (sign is stored in the numerator)
- Special handling for edge cases like division by zero, infinity, and NaN
- Uses `num-integer` and `num-traits` crates for mathematical operations on generic integers
- Optional features for std support and big integer support

## Building and Running
- Build: `cargo build`
- Run tests: `cargo test`
- Build documentation: `cargo doc`
- Check formatting: `cargo fmt --check`
- Run clippy lints: `cargo clippy`

## Development Conventions
- Uses Rust edition 2021
- Clippy lints are disabled for "suspicious arithmetic" due to custom implementation
- Extensive test coverage with both unit tests and quickcheck property-based tests
- API documentation using Rustdoc format
- Optimized for size in release builds (using `opt-level = 'z'`)
- Supports no_std environments (commented out in current version)

## Notable Functions
- `Fraction::new(numer, denom)` - Creates a normalized fraction
- `Fraction::new_raw(numer, denom)` - Creates a fraction without normalization
- `const_gcd(m, n)` - Calculates greatest common divisor
- `const_abs(a)` - Returns absolute value
- `archimedes(q_1, q_2, q_3)` - Calculates triangle area using Archimedes' formula
- `cross()` - Calculates cross product for fraction comparison without floating point errors

## Testing
The project includes comprehensive unit tests covering:
- Basic fraction construction and normalization
- Arithmetic operations
- Comparison operations
- Special value handling
- Property-based testing with quickcheck
- Edge cases and overflow scenarios