# Agent Guidelines for fractions-rs

## Project Overview
Rust library for fractional number arithmetic with generic integer types. Supports no_std environments with optional std/bigint features.

## Build & Test Commands

### Essential Commands
```bash
# Build
cargo build

# Test all features
cargo test --all-features --workspace

# Run single test (standard Rust pattern)
cargo test test_archimedes4
cargo test fractions::tests::test_new

# Run tests in specific module
cargo test fractions

# Lint
cargo clippy --all-targets --all-features --workspace

# Format check
cargo fmt --all --check

# Auto-format
cargo fmt --all

# Run benchmarks (Criterion)
cargo bench

# Specific benchmark group
cargo bench bench_fraction_creation

# Documentation
cargo doc --no-deps --document-private-items --all-features --workspace --examples
```

### CI Pipeline
GitHub Actions runs: test, rustfmt check, clippy, docs, security audit, multi-toolchain testing.

## Code Style Guidelines

### Naming Conventions
- **Functions/Methods**: snake_case, descriptive names
- **Types**: PascalCase, generic type parameters use single uppercase letters (T)
- **Variables**: snake_case, no abbreviations (e.g., `normalize` not `norm`)
- **Predicates**: `is_*` prefix (e.g., `is_zero()`, `is_infinite()`, `is_nan()`)
- **Mutators**: `set_*` prefix (e.g., `set_zero()`, `set_infinite()`)
- **Tests**: `test_<function>` for unit tests, `check_<function>` for property tests
- **Benchmarks**: `bench_<category>_<operation>` pattern

### Imports
- Core crate imports (`core::`) before external crates
- Group by source, alphabetically within groups
- Explicit imports only (no `use *;`)
- Example:
```rust
use core::ops::{Add, Div, Mul, Neg};
use num_integer::gcd;
use num_traits::{One, Signed, Zero};
```

### Code Formatting
- 4-space indentation
- K&R brace style (opening brace on same line)
- Trailing commas in multi-line lists
- Spaces around operators and after commas
- Uses default rustfmt settings (no custom config)

### Documentation
- Module-level: `//!` with overview and compatibility notes
- Item-level: `///` with description, Arguments, Returns, and Examples sections
- All public APIs must have documentation
- Examples use `assert_eq!` for verification

## Implementation Patterns

### Fraction Special Values
- Zero: `Fraction::zero()` or `new(0, 1)`
- Infinity: `new(1, 0)` or `new(-1, 0)`
- NaN: `new(0, 0)`
- Denominator is always kept positive (sign stored in numerator)

### Error Handling
- Panic-based (implicit through trait bounds)
- No Result/Option types in public API
- Special values (∞, NaN) are valid states, not errors
- Document panics but don't explicitly handle

### Testing
- Unit tests inline: `#[cfg(test)] mod tests { ... }`
- Property-based tests: quickcheck with `#[quickcheck]` macro
- Comprehensive edge case coverage (infinity, NaN, zero, overflow)
- 33+ test functions across codebase

### Attributes & Macros
- Use `#[inline]` for small functions
- `#[allow(missing_docs)]` on Fraction struct (fields self-documenting)
- `#[allow(clippy::suspicious_*_impl)]` at crate level for custom arithmetic
- Macros reduce boilerplate in trait implementations

## Project Structure
```
src/
├── lib.rs           # Entry point, exports, archimedes helper
├── fractions.rs     # Main Fraction implementation (1,966 lines)
└── main.rs          # Placeholder binary
benches/
└── fraction_benchmarks.rs  # Criterion benchmarks
```

## Recent Enhancements

### Added Features (2026-01-23)
- **FromStr implementation**: Parse fraction strings like `"1/2"`, `"-3/4"`, `"inf"`, `"nan"`
- **Display formatting**: Added `to_decimal()` and `to_mixed_fraction()` methods
- **Math operations**: Added `pow()`, `approx_eq()`, `floor()`, `ceil()` methods

### Developer Tooling Added
- **Pre-commit hooks**: `.pre-commit-config.yaml` with cargo fmt, clippy checks
- **Release automation**: `release.toml` for cargo-release integration
- **Examples directory**: `examples/financial.rs`, `examples/measurement.rs` with real-world usage

### Configuration Files Created
- `.pre-commit-config.yaml`: Pre-commit hooks for formatting and linting
- `release.toml`: Cargo-release configuration for automated releases
- `AGENTS.md`: This file for agentic development guidance

## Before Committing
1. Run `cargo test --all-features --workspace`
2. Run `cargo clippy --all-targets --all-features --workspace`
3. Run `cargo fmt --all --check`
4. Update CHANGELOG.md under "Unreleased" section
5. Ensure all public APIs have doc comments with examples
