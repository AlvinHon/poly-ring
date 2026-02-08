use std::ops::{Range, RangeInclusive};

use num::Zero;
use rand::distr::{
    uniform::{SampleBorrow, SampleRange, SampleUniform, UniformSampler},
    Distribution, StandardUniform, Uniform,
};

use crate::Polynomial;

/// A sampler for random polynomials.
/// It generates a polynomial (deg of N-1) with random coefficients in a range defined by `low` and `high`.
/// I.e. the bound given by the minimum coefficient of `low` polynomial and the maximum coefficient of `high` polynomial.
///
/// # Example
///
/// ```
/// use rand::{Rng, distr::uniform::UniformSampler};
/// use poly_ring_xnp1::{Polynomial, rand::PolynomialSampler};
///
/// let rng = &mut rand::rng();
///
/// let p1 = Polynomial::<i32, 4>::new(vec![1, 2, 3, 4]);
/// let p2 = Polynomial::<i32, 4>::new(vec![5, 6, 7, 8]);
/// assert!(PolynomialSampler::new(p2.clone(), p1.clone()).is_err()); // max coeffs of right < min coeffs of left
/// let s = PolynomialSampler::new(p1, p2).unwrap();
/// let p = s.sample(rng);
/// p.iter().for_each(|c| assert!(1 <= *c && *c < 8));
/// ```
pub struct PolynomialSampler<T, const N: usize>(Uniform<T>)
where
    T: Zero + PartialOrd + Ord + SampleUniform;

impl<T, const N: usize> UniformSampler for PolynomialSampler<T, N>
where
    T: Zero + PartialOrd + Ord + SampleUniform,
{
    type X = Polynomial<T, N>;

    fn new<B1, B2>(low: B1, high: B2) -> Result<Self, rand::distr::uniform::Error>
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        let low = low.borrow().iter().min();
        let high = high.borrow().iter().max();

        match (low, high) {
            (Some(low), Some(high)) if high >= low => {
                Uniform::<T>::new(low, high).map(PolynomialSampler)
            }
            _ => Err(rand::distr::uniform::Error::EmptyRange),
        }
    }

    fn new_inclusive<B1, B2>(low: B1, high: B2) -> Result<Self, rand::distr::uniform::Error>
    where
        B1: SampleBorrow<Self::X> + Sized,
        B2: SampleBorrow<Self::X> + Sized,
    {
        UniformSampler::new(low, high)
    }

    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> Self::X {
        let coeffs = (0..N).map(|_| self.0.sample(rng)).collect();
        Polynomial::new(coeffs)
    }
}

impl<T, const N: usize> SampleUniform for Polynomial<T, N>
where
    T: Zero + PartialOrd + Ord + SampleUniform,
{
    type Sampler = PolynomialSampler<T, N>;
}

impl<T, const N: usize> Distribution<Polynomial<T, N>> for StandardUniform
where
    T: Zero,
    StandardUniform: Distribution<T>,
{
    fn sample<R: rand::RngExt + ?Sized>(&self, rng: &mut R) -> Polynomial<T, N> {
        let coeffs = (0..N).map(|_| rng.random()).collect();
        Polynomial::new(coeffs)
    }
}

/// A range of coefficients for random polynomials.
/// It is used to generate a polynomial with random coefficients in a given range.
///
/// # Example
///
/// ```
/// use rand::RngExt;
/// use poly_ring_xnp1::{Polynomial, rand::CoeffsRange};
///
/// let rng = &mut rand::rng();
///
/// let r = CoeffsRange::from(-2..3);
/// let p: Polynomial<i32, 4> = rng.random_range(r);
/// p.iter().for_each(|c| assert!(-2 <= *c && *c < 3));
/// ```
#[derive(Clone, Debug)]
pub struct CoeffsRange<T> {
    range: Range<T>,
}

impl<T> From<Range<T>> for CoeffsRange<T> {
    fn from(range: Range<T>) -> Self {
        CoeffsRange { range }
    }
}

/// An inclusive range of coefficients for random polynomials.
/// It is used to generate a polynomial with random coefficients in a given inclusive range.
///
/// # Example
///
/// ```
/// use rand::RngExt;
/// use poly_ring_xnp1::{Polynomial, rand::CoeffsRangeInclusive};
///
/// let rng = &mut rand::rng();
///
/// let r = CoeffsRangeInclusive::from(-3..=3);
/// let p: Polynomial<i32, 4> = rng.random_range(r);
/// p.iter().for_each(|c| assert!(-3 <= *c && *c <= 3));
/// ```
#[derive(Clone, Debug)]
pub struct CoeffsRangeInclusive<T> {
    range: RangeInclusive<T>,
}

impl<T> From<RangeInclusive<T>> for CoeffsRangeInclusive<T> {
    fn from(range: RangeInclusive<T>) -> Self {
        CoeffsRangeInclusive { range }
    }
}

macro_rules! impl_samplerange {
    ($P:ty, $C:ty) => {
        impl<T, const N: usize> SampleRange<$P> for $C
        where
            T: Clone + PartialOrd + Zero + SampleUniform,
        {
            fn sample_single<R: rand::RngExt + ?Sized>(
                self,
                rng: &mut R,
            ) -> Result<Polynomial<T, N>, rand::distr::uniform::Error> {
                let mut coeffs = Vec::with_capacity(N);
                for _ in 0..N {
                    let c = match self.range.clone().sample_single(rng) {
                        Ok(c) => c,
                        Err(e) => return Err(e),
                    };
                    coeffs.push(c);
                }
                Ok(Polynomial::new(coeffs))
            }

            fn is_empty(&self) -> bool {
                self.range.is_empty()
            }
        }
    };
}

impl_samplerange!(Polynomial<T, N>, CoeffsRange<T>);
impl_samplerange!(Polynomial<T, N>, CoeffsRangeInclusive<T>);

#[cfg(test)]
mod tests {
    use rand::RngExt;

    use super::*;

    #[test]
    fn test_random_polynomial() {
        let rng = &mut rand::rng();

        let p: Polynomial<i32, 4> = rng.random();
        assert!(p.deg() <= 3);
    }

    #[cfg(feature = "zq")]
    #[test]
    fn test_random_polynomial_over_zq() {
        use crate::zq::{ZqI32, ZqI64, ZqU32, ZqU64};
        let rng = &mut rand::rng();

        let p: Polynomial<ZqI32<7>, 4> = rng.random();
        assert!(p.deg() <= 3);

        let p: Polynomial<ZqI64<7>, 4> = rng.random();
        assert!(p.deg() <= 3);

        let p: Polynomial<ZqU32<7>, 4> = rng.random();
        assert!(p.deg() <= 3);

        let p: Polynomial<ZqU64<7>, 4> = rng.random();
        assert!(p.deg() <= 3);

        // .. test sampler ..
        let p1 = Polynomial::<ZqI32<23>, 4>::new(vec![1, 2, 3, 4]);
        let p2 = Polynomial::<ZqI32<23>, 4>::new(vec![5, 6, 7, 8]);
        assert!(PolynomialSampler::new(p2.clone(), p1.clone()).is_err()); // max coeffs of right < min coeffs of left
        let s = PolynomialSampler::new(p1.clone(), p2.clone()).unwrap();
        let p = s.sample(rng);
        p.iter()
            .for_each(|c| assert!(ZqI32::<23>::from(1) <= *c && *c < ZqI32::<23>::from(8)));
        let s = PolynomialSampler::new_inclusive(p1, p2).unwrap();
        let p = s.sample(rng);
        p.iter()
            .for_each(|c| assert!(ZqI32::<23>::from(1) <= *c && *c <= ZqI32::<23>::from(8)));

        // .. test coeffs range ..

        let r = CoeffsRange::from(ZqI32::<23>::from(-2)..ZqI32::<23>::from(3));
        let p: Polynomial<ZqI32<23>, 4> = rng.random_range(r);
        p.iter()
            .for_each(|c| assert!(ZqI32::<23>::from(-2) <= *c && *c < ZqI32::<23>::from(3)));

        // .. test coeffs range inclusive ..

        let r = CoeffsRangeInclusive::from(ZqI32::<23>::from(-3)..=ZqI32::<23>::from(3));
        let p: Polynomial<ZqI32<23>, 4> = rng.random_range(r);
        p.iter()
            .for_each(|c| assert!(ZqI32::<23>::from(-3) <= *c && *c < ZqI32::<23>::from(3)));
    }

    #[cfg(feature = "zq")]
    #[test]
    #[should_panic]
    fn test_random_sample_empty_range() {
        use crate::zq::ZqI32;
        let rng = &mut rand::rng();

        let empty_range = CoeffsRange::from(ZqI32::<23>::from(3)..ZqI32::<23>::from(3));
        let _: Polynomial<ZqI32<23>, 4> = rng.random_range(empty_range);
    }
}
