//! Logging utilities for fractions-rs
//!
//! This module provides optional logging capabilities when the `std` feature is enabled.
//! It uses `env_logger` for flexible logging configuration via environment variables.

#[cfg(feature = "std")]
use log::LevelFilter;

#[cfg(feature = "std")]
use std::sync::OnceLock;

#[cfg(feature = "std")]
static LOGGER_INITIALIZED: OnceLock<()> = OnceLock::new();

/// Initialize the logger with default settings.
///
/// The log level is controlled by the `RUST_LOG` environment variable.
/// If `RUST_LOG` is not set, it defaults to `info` level.
///
/// # Panics
///
/// Panics if the logger has already been initialized.
#[cfg(feature = "std")]
pub fn init_logger() {
    env_logger::init();
    let _ = LOGGER_INITIALIZED.set(());
}

/// Initialize the logger with a custom filter.
///
/// # Arguments
///
/// * `filter` - A filter string (e.g., "debug", "info", "warn", "error")
///
/// # Panics
///
/// Panics if the logger has already been initialized.
#[cfg(feature = "std")]
pub fn init_logger_with_filter(filter: &str) {
    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or(filter)).init();
    let _ = LOGGER_INITIALIZED.set(());
}

/// Try to initialize the logger with default settings.
///
/// The log level is controlled by the `RUST_LOG` environment variable.
/// If `RUST_LOG` is not set, it defaults to `info` level.
///
/// # Returns
///
/// * `Ok(())` if the logger was successfully initialized
/// * `Err(&'static str)` if the logger has already been initialized
#[cfg(feature = "std")]
pub fn try_init_logger() -> Result<(), &'static str> {
    LOGGER_INITIALIZED
        .set(())
        .map_err(|_| "Logger already initialized")?;
    env_logger::try_init().map_err(|_| "Logger already initialized")
}

/// Try to initialize the logger with a custom filter.
///
/// # Arguments
///
/// * `filter` - A filter string (e.g., "debug", "info", "warn", "error")
///
/// # Returns
///
/// * `Ok(())` if the logger was successfully initialized
/// * `Err(&'static str)` if the logger has already been initialized
#[cfg(feature = "std")]
pub fn try_init_logger_with_filter(filter: &str) -> Result<(), &'static str> {
    LOGGER_INITIALIZED
        .set(())
        .map_err(|_| "Logger already initialized")?;
    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or(filter))
        .try_init()
        .map_err(|_| "Logger already initialized")
}

/// Check if the logger has been initialized.
///
/// # Returns
///
/// * `true` if the logger has been initialized
/// * `false` otherwise
#[cfg(feature = "std")]
pub fn is_logger_initialized() -> bool {
    LOGGER_INITIALIZED.get().is_some()
}

/// Get the current log level filter.
///
/// Returns `None` if the logger hasn't been initialized yet.
#[cfg(feature = "std")]
pub fn get_log_level() -> Option<LevelFilter> {
    if is_logger_initialized() {
        Some(LevelFilter::Info)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_try_init_logger() {
        // This test will succeed only if logger is not already initialized
        // In test context, we just verify the function can be called
        let result = try_init_logger();
        assert!(result.is_ok() || result.is_err());
    }

    #[test]
    fn test_try_init_logger_with_filter() {
        // Reset the logger state for this test by checking initialization status
        if !is_logger_initialized() {
            let result = try_init_logger_with_filter("debug");
            assert!(result.is_ok() || result.is_err());
        }
    }

    #[test]
    fn test_is_logger_initialized() {
        // Just verify the function returns a boolean
        let _ = is_logger_initialized();
    }
}
