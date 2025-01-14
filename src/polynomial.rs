use crate::{
    arith::{self, trim_zeros},
    modulo::PolynomialModulo,
};
use num::{One, Zero};
use std::ops::{Add, Mul, Neg, Sub};

/// Polynomial implemented by a vector of coefficients of type `T` with
/// operations defined in Zp\[X\]/(x^n + 1). **The constant N must be a power of two.**
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Polynomial<T, const N: usize> {
    pub(crate) coeffs: Vec<T>,
}

impl<T, const N: usize> Polynomial<T, N> {
    /// Creates a new polynomial within Z[x]/[x^n + 1] with the given coefficients.
    ///
    /// p(x) = coeffs\[0\] + coeffs\[1\] * x + coeffs\[2\] * x^2 + ...
    ///
    /// ## Safety
    /// The constant N must be a power of two, so that the polynomial is irreducible over Z.
    pub fn new(coeffs: Vec<T>) -> Self
    where
        T: Zero,
    {
        assert_eq!(N.count_ones(), 1, "N must be a power of two");
        assert!(
            coeffs.len() <= N,
            "The degree of the polynomial must be less than or equal to N"
        );

        let mut coeffs = coeffs;
        trim_zeros(&mut coeffs);

        Polynomial { coeffs }
    }

    /// Creates a new polynomial within Z[x]/[x^n + 1] by applying modulo x^n + 1 of a the input
    /// polynomial with the given coefficients (length can be larger than N).
    ///
    /// p(x) = coeffs\[0\] + coeffs\[1\] * x + coeffs\[2\] * x^2 + ...
    ///
    /// ## Safety
    /// The constant N must be a power of two, so that the polynomial is irreducible over Z.
    pub fn from_coeffs(coeffs: Vec<T>) -> Self
    where
        T: Zero + One + Clone,
        for<'a> &'a T: Mul<Output = T> + Sub<Output = T> + Add<Output = T>,
    {
        assert_eq!(N.count_ones(), 1, "N must be a power of two");

        let mut coeffs = coeffs;
        trim_zeros(&mut coeffs);

        arith::modulo(&Polynomial { coeffs }, &PolynomialModulo::<T, N>::new())
    }

    /// Returns the degree of the polynomial.
    ///
    /// ## Panics
    /// Panics if the input is an empty vector.
    pub fn deg(&self) -> usize {
        self.coeffs.len() - 1
    }

    /// Returns the leading coefficient of the polynomial.
    pub fn leading_coefficient(&self) -> T
    where
        T: Zero + Clone,
    {
        self.coeffs.last().cloned().unwrap_or_else(T::zero)
    }

    /// Returns the coefficient of the term with the given degree.
    pub fn coefficient(&self, idx: usize) -> T
    where
        T: Zero + Clone,
    {
        self.coeffs.get(idx).cloned().unwrap_or_else(T::zero)
    }

    /// Maps the polynomial coefficients to another type.
    pub fn mapv<U, F>(&self, f: F) -> Polynomial<U, N>
    where
        F: Fn(&T) -> U,
    {
        Polynomial {
            coeffs: self.coeffs.iter().map(f).collect(),
        }
    }

    /// Returns an iterator over the polynomial coefficients.
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.coeffs.iter()
    }
}

impl<T, const N: usize> One for Polynomial<T, N>
where
    T: Zero + One + Clone,
    for<'a> &'a T: Mul<Output = T> + Sub<Output = T> + Add<Output = T>,
{
    fn one() -> Self {
        Polynomial {
            coeffs: vec![T::one()],
        }
    }
}

impl<T, const N: usize> Zero for Polynomial<T, N>
where
    T: Zero + One + Clone,
    for<'a> &'a T: Mul<Output = T> + Sub<Output = T> + Add<Output = T>,
{
    fn zero() -> Self {
        Polynomial { coeffs: vec![] }
    }

    fn is_zero(&self) -> bool {
        self.coeffs.is_empty() || self.coeffs.iter().all(|c| c.is_zero())
    }
}

// ... impl ops::* for Polynomial<T> ...

impl<T, const N: usize> Add for Polynomial<T, N>
where
    T: Zero + One + Clone,
    for<'a> &'a T: Mul<Output = T> + Sub<Output = T> + Add<Output = T>,
{
    type Output = Self;

    #[allow(clippy::needless_borrow)]
    fn add(self, other: Self) -> Self {
        let ret = arith::add(&self, &other);
        let modulo = PolynomialModulo::<T, N>::new();
        arith::modulo(&ret, &modulo)
    }
}

impl<T, const N: usize> Neg for Polynomial<T, N>
where
    T: Zero + Clone,
    for<'a> &'a T: Neg<Output = T>,
{
    type Output = Self;

    fn neg(self) -> Self {
        let mut result = self;
        result.coeffs.iter_mut().for_each(|c| *c = -&*c);
        result
    }
}

impl<T, const N: usize> Sub for Polynomial<T, N>
where
    T: Zero + One + Clone,
    for<'a> &'a T: Neg<Output = T> + Mul<Output = T> + Sub<Output = T> + Add<Output = T>,
{
    type Output = Self;

    #[allow(clippy::needless_borrow)]
    fn sub(self, other: Self) -> Self {
        let ret = arith::add(&self, &(-other));
        let modulo = PolynomialModulo::<T, N>::new();
        arith::modulo(&ret, &modulo)
    }
}

impl<T, const N: usize> Mul for Polynomial<T, N>
where
    T: Zero + One + Clone,
    for<'a> &'a T: Mul<Output = T> + Add<Output = T> + Sub<Output = T>,
{
    type Output = Self;

    #[allow(clippy::needless_borrow)]
    fn mul(self, other: Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Polynomial::zero();
        }
        // Different with arith::mul, this applies modulo operation.
        arith::cyclic_mul(&self, &other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const N: usize = 512; // power of two

    #[test]
    #[should_panic]
    fn test_new() {
        const INVALID_N: usize = 511;
        Polynomial::<i32, INVALID_N>::new(vec![1, 2, 3]);
    }

    #[test]
    fn test_from_coeffs() {
        let p = Polynomial::<i32, 4>::from_coeffs(vec![1, 2, 3, 4, 5]);
        assert_eq!(p.coeffs, vec![-4, 2, 3, 4]);
    }

    #[test]
    fn test_zero() {
        let p = Polynomial::<i32, N>::zero();
        assert!(p.is_zero());
    }

    #[test]
    fn test_deg() {
        let p = Polynomial::<i32, N>::new(vec![1, 2, 3]);
        assert_eq!(p.deg(), 2);
    }

    #[test]
    fn test_leading_coefficient() {
        let p = Polynomial::<i32, N>::new(vec![1, 2, 3]);
        assert_eq!(p.leading_coefficient(), 3);
    }

    #[test]
    fn test_mapv() {
        let p = Polynomial::<i32, N>::new(vec![1, 2, 3]);
        let q = p.mapv(|c| *c as i64);
        assert_eq!(q.coeffs, vec![1i64, 2, 3]);
    }

    #[test]
    fn test_iter() {
        let p = Polynomial::<i32, N>::new(vec![1, 2, 3]);
        let mut iter = p.iter();
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), None);
    }
}
