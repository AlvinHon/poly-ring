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
    /// ## Example
    /// ```
    /// use poly_ring_xnp1::Polynomial;
    /// // p(x) = 1 + 2x + 3x^2
    /// let p = Polynomial::<i32, 4>::new(vec![1, 2, 3]);
    /// assert_eq!(p.deg(), 2);
    /// ```
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
    /// ## Example
    ///
    /// ```
    /// use poly_ring_xnp1::Polynomial;
    ///
    /// // p(x) = (1 + 2x + 3x^2 + 4x^3 + 5x^4) mod (x^4 + 1)
    /// let p = Polynomial::<i32, 4>::from_coeffs(vec![1, 2, 3, 4, 5]);
    /// let mut coeffs_itr = p.iter();
    /// assert_eq!(coeffs_itr.next(), Some(&-4));
    /// assert_eq!(coeffs_itr.next(), Some(&2));
    /// assert_eq!(coeffs_itr.next(), Some(&3));
    /// assert_eq!(coeffs_itr.next(), Some(&4));
    /// assert_eq!(coeffs_itr.next(), None);
    /// ```
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

        arith::modulo(Polynomial { coeffs }, PolynomialModulo::<T, N>::new())
    }

    /// Returns the degree of the polynomial.
    ///
    /// ## Example
    ///
    /// ```
    /// use poly_ring_xnp1::Polynomial;
    ///
    /// // p(x) = 1 + 2x + 3x^2
    /// let p = Polynomial::<i32, 4>::new(vec![1, 2, 3]);
    /// assert_eq!(p.deg(), 2);
    /// ```
    ///
    /// ## Panics
    /// Panics if the input is an empty vector.
    pub fn deg(&self) -> usize {
        self.coeffs.len() - 1
    }

    /// Returns the leading coefficient of the polynomial. If the polynomial is zero, it returns 0 (T::zero).
    ///
    /// ## Example
    ///
    /// ```
    /// use poly_ring_xnp1::Polynomial;
    ///
    /// // p(x) = 1 + 2x + 3x^2
    /// let p = Polynomial::<i32, 4>::new(vec![1, 2, 3]);
    /// assert_eq!(p.leading_coefficient(), 3);
    /// ```
    pub fn leading_coefficient(&self) -> T
    where
        T: Zero + Clone,
    {
        self.coeffs.last().cloned().unwrap_or_else(T::zero)
    }

    /// Returns the coefficient of the term with the given degree.
    ///
    /// ## Example
    /// ```
    /// use poly_ring_xnp1::Polynomial;
    ///
    /// // p(x) = 1 + 2x + 3x^2
    /// let p = Polynomial::<i32, 4>::new(vec![1, 2, 3]);
    /// assert_eq!(p.coefficient(0), 1);
    /// assert_eq!(p.coefficient(1), 2);
    /// assert_eq!(p.coefficient(2), 3);
    /// assert_eq!(p.coefficient(3), 0); // 0 (T::zero) for the missing term
    /// ```
    pub fn coefficient(&self, idx: usize) -> T
    where
        T: Zero + Clone,
    {
        self.coeffs.get(idx).cloned().unwrap_or_else(T::zero)
    }

    /// Maps the polynomial coefficients to another type.
    ///
    /// ## Example
    ///
    /// ```
    /// use poly_ring_xnp1::Polynomial;
    ///
    /// // p(x) = 1 + 2x + 3x^2
    /// let p = Polynomial::<i32, 4>::new(vec![1, 2, 3]);
    /// let q = p.mapv(|c| *c as i64);
    /// assert_eq!(q.coefficient(0), 1i64);
    /// assert_eq!(q.coefficient(1), 2i64);
    /// assert_eq!(q.coefficient(2), 3i64);
    /// ```
    pub fn mapv<U, F>(&self, f: F) -> Polynomial<U, N>
    where
        U: Zero,
        F: Fn(&T) -> U,
    {
        let mut coeffs = self.coeffs.iter().map(f).collect();
        trim_zeros(&mut coeffs);

        Polynomial { coeffs }
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

    fn add(self, other: Self) -> Self {
        let ret = arith::add(self, other);
        let modulo = PolynomialModulo::<T, N>::new();
        arith::modulo(ret, modulo)
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

    fn sub(self, other: Self) -> Self {
        let ret = arith::add(self, -other);
        let modulo = PolynomialModulo::<T, N>::new();
        arith::modulo(ret, modulo)
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

    #[test]
    #[should_panic]
    fn test_new() {
        const INVALID_N: usize = 5;
        Polynomial::<i32, INVALID_N>::new(vec![1, 2, 3]);
    }

    #[test]
    fn test_zero() {
        let p = Polynomial::<i32, 4>::zero();
        assert!(p.is_zero());
    }
}
