use std::marker::PhantomData;

use num::{One, Zero};

/// Polynomial Modulo implemented by a vector of terms (degree, coefficient) in sparse vector representation.
/// It is typically used as the polynomial `x^n + 1` in this library.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub(crate) struct PolynomialModulo<T, const N: usize> {
    phantom: PhantomData<T>,
}

impl<T, const N: usize> PolynomialModulo<T, N> {
    pub fn new() -> Self {
        PolynomialModulo {
            phantom: PhantomData,
        }
    }

    pub fn deg(&self) -> usize {
        N
    }

    pub fn leading_coefficient(&self) -> T
    where
        T: Zero + One + Clone,
    {
        T::one()
    }

    pub fn coefficient(&self, idx: usize) -> T
    where
        T: Zero + One + Clone,
    {
        if idx == N || idx == 0 {
            T::one()
        } else {
            T::zero()
        }
    }
}
