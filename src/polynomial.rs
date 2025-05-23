use crate::{
    arith::{self, trim_zeros},
    modulo::PolynomialModulus,
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
    pub fn new<K>(coeffs: Vec<K>) -> Self
    where
        T: Zero + From<K>,
    {
        assert_eq!(N.count_ones(), 1, "N must be a power of two");
        assert!(
            coeffs.len() <= N,
            "The degree of the polynomial must be less than or equal to N"
        );

        let mut coeffs = coeffs.into_iter().map(T::from).collect();
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

        arith::modulo(Polynomial { coeffs }, PolynomialModulus::<T>::new(N))
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
    /// Panics if the coefficients is an empty vector.
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

    /// Iterates over the polynomial coefficients and applies the given mutation function.
    ///
    /// ```
    /// use poly_ring_xnp1::Polynomial;
    /// use num::Zero;
    ///
    /// // p(x) = 1 + 2x + 3x^2
    /// let mut p = Polynomial::<i32, 4>::new(vec![1, 2, 3]);
    /// p.coeffs_mut(|c| *c = 0);
    /// assert!(p.is_zero());
    /// ```
    pub fn coeffs_mut<F>(&mut self, f: F)
    where
        T: Zero,
        F: FnMut(&mut T),
    {
        self.coeffs.iter_mut().for_each(f);
        trim_zeros(&mut self.coeffs);
    }

    /// Returns an iterator over the polynomial coefficients, where the polynomial
    /// is represented by p(x) = coeffs\[0\] + coeffs\[1\] * x + coeffs\[2\] * x^2 + ...
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
        let modulo = PolynomialModulus::<T>::new(N);
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
        let modulo = PolynomialModulus::<T>::new(N);
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

// ... impl serde::(De)Serialize for Polynomial<T> ...
#[cfg(feature = "serde")]
impl<T, const N: usize> serde::Serialize for Polynomial<T, N>
where
    T: serde::Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.coeffs.serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de, T, const N: usize> serde::Deserialize<'de> for Polynomial<T, N>
where
    T: serde::Deserialize<'de> + Zero,
{
    fn deserialize<D>(deserializer: D) -> Result<Polynomial<T, N>, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let coeffs = Vec::<T>::deserialize(deserializer)?;
        Ok(Polynomial::new(coeffs))
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    #[should_panic]
    fn test_new_invalid_n() {
        const INVALID_N: usize = 5;
        Polynomial::<i32, INVALID_N>::new(vec![1, 2, 3]);
    }

    #[test]
    #[should_panic]
    fn test_new_invalid_coeffs() {
        Polynomial::<i32, 4>::new(vec![1, 2, 3, 4, 5, 6, 7, 8]);
    }

    #[test]
    #[should_panic]
    fn test_from_coeffs_invalid_n() {
        const INVALID_N: usize = 5;
        Polynomial::<i32, INVALID_N>::from_coeffs(vec![1, 2, 3]);
    }

    #[test]
    fn test_zero() {
        let p = Polynomial::<i32, 4>::zero();
        assert!(p.is_zero());
        assert!(p.leading_coefficient().is_zero());

        let q = Polynomial::<i32, 4>::new(vec![1, 2, 3]);
        assert_eq!(p.clone() * q.clone(), Polynomial::zero());
        assert_eq!(q.clone() * p.clone(), Polynomial::zero());
    }

    #[test]
    fn test_sub() {
        let p1 = Polynomial::<i32, 4>::new(vec![1, 2, 3]);
        let p2 = Polynomial::new(vec![4, 5]);
        let r = p1.clone() - p2.clone();
        assert_eq!(r.coeffs, vec![-3, -3, 3]);
    }

    #[cfg(feature = "zq")]
    #[test]
    fn test_poly_over_zq() {
        use crate::zq::{ZqI32, ZqI64, ZqU32, ZqU64};

        // p is the polynomial 1 + 2x + 3x^2 where the coefficients are in Z/7Z.
        let p = Polynomial::<ZqI32<7>, 4>::new(vec![1i32, 2, 3]);
        assert_eq!(p.deg(), 2);
        assert_eq!(p.coefficient(0), ZqI32::new(1));
        assert_eq!(p.coefficient(1), ZqI32::new(2));
        assert_eq!(p.coefficient(2), ZqI32::new(3));

        let p = Polynomial::<ZqI64<7>, 4>::new(vec![1i64, 2, 3]);
        assert_eq!(p.deg(), 2);
        assert_eq!(p.coefficient(0), ZqI64::new(1));
        assert_eq!(p.coefficient(1), ZqI64::new(2));
        assert_eq!(p.coefficient(2), ZqI64::new(3));

        let p = Polynomial::<ZqU32<7>, 4>::new(vec![1u32, 2, 3]);
        assert_eq!(p.deg(), 2);
        assert_eq!(p.coefficient(0), ZqU32::new(1));
        assert_eq!(p.coefficient(1), ZqU32::new(2));
        assert_eq!(p.coefficient(2), ZqU32::new(3));

        let p = Polynomial::<ZqU64<7>, 4>::new(vec![1u64, 2, 3]);
        assert_eq!(p.deg(), 2);
        assert_eq!(p.coefficient(0), ZqU64::new(1));
        assert_eq!(p.coefficient(1), ZqU64::new(2));
        assert_eq!(p.coefficient(2), ZqU64::new(3));
    }
}
