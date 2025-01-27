use std::marker::PhantomData;

use num::{One, Zero};

/// Represents a Polynomial Modulus `x^n + alpha` used in polynomial division algorithm in this library.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub(crate) struct PolynomialModulus<T>
where
    T: One + Zero + Clone,
{
    n: usize,
    alpha: T,
    phantom: PhantomData<T>,
}

impl<T> PolynomialModulus<T>
where
    T: One + Zero + Clone,
{
    /// Creates a new polynomial modulus `x^n + 1`.
    pub fn new(n: usize) -> Self {
        Self::new_with_alpha(n, T::one())
    }

    /// Creates a new polynomial modulus `x^n + alpha`.
    pub fn new_with_alpha(n: usize, alpha: T) -> Self {
        PolynomialModulus {
            n,
            alpha,
            phantom: PhantomData,
        }
    }

    pub fn deg(&self) -> usize {
        self.n
    }

    pub fn leading_coefficient(&self) -> T {
        T::one()
    }

    pub fn coefficient(&self, idx: usize) -> T {
        if idx == self.n {
            T::one()
        } else if idx == 0 {
            self.alpha.clone()
        } else {
            T::zero()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_polynomial_modulus() {
        // x^4 + 1
        let modulus = PolynomialModulus::<i32>::new(4);
        assert_eq!(modulus.deg(), 4);
        assert_eq!(modulus.leading_coefficient(), 1);
        assert_eq!(modulus.coefficient(0), 1);
        assert_eq!(modulus.coefficient(1), 0);
        assert_eq!(modulus.coefficient(2), 0);
        assert_eq!(modulus.coefficient(3), 0);
        assert_eq!(modulus.coefficient(4), 1);

        // x^4 - 1
        let modulus = PolynomialModulus::<i32>::new_with_alpha(4, -1);
        assert_eq!(modulus.deg(), 4);
        assert_eq!(modulus.leading_coefficient(), 1);
        assert_eq!(modulus.coefficient(0), -1);
        assert_eq!(modulus.coefficient(1), 0);
        assert_eq!(modulus.coefficient(2), 0);
        assert_eq!(modulus.coefficient(3), 0);
        assert_eq!(modulus.coefficient(4), 1);
    }
}
