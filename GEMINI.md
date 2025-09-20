# Gemini Code Assistant Context

## Project Overview

This project is a Rust library for working with fractions. It provides a `Fraction` struct that can be used to represent and manipulate fractional numbers. The library includes functionality for:

*   Creating fractions from numerators and denominators.
*   Normalizing fractions to their simplest form.
*   Performing arithmetic operations (addition, subtraction, multiplication, division).
*   Comparing fractions.
*   Handling special cases like infinity and NaN (Not a Number).

The core logic is implemented in `src/fractions.rs`, and the main library entry point is `src/lib.rs`. The project uses the `num-bigint`, `num-integer`, and `num-traits` crates for numerical operations.

## Building and Running

### Building

To build the project, run the following command:

```bash
cargo build
```

### Running Tests

To run the test suite, use the following command:

```bash
cargo test --all-features --workspace
```

### Checking Formatting

To check the code formatting, run:

```bash
cargo fmt --all --check
```

### Linting

To run the linter, use the following command:

```bash
cargo clippy --all-targets --all-features --workspace
```

### Generating Documentation

To generate the documentation, run:

```bash
cargo doc --no-deps --document-private-items --all-features --workspace --examples
```

## Development Conventions

*   **Code Style:** The project follows the standard Rust formatting guidelines, enforced by `rustfmt`.
*   **Testing:** The project has a comprehensive test suite, including unit tests and property-based tests using `quickcheck`. Tests are located in the same files as the implementation, and in the `tests` directory.
*   **Contributions:** The project has a `CONTRIBUTING.md` file with contribution guidelines.
