#![doc = include_str!("../README.md")]

pub(crate) mod arith;
pub(crate) mod modulo;
pub mod polynomial;
pub use polynomial::Polynomial;

#[cfg(feature = "zq")]
pub mod zq;

#[cfg(feature = "rand")]
pub mod rand;
