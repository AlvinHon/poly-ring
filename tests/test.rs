use std::ops::RangeInclusive;

use num::{One, Zero};
use poly_ring_xnp1::Polynomial;
use rand::{distr::uniform::SampleUniform, rng, Rng};

const N: usize = 512; // power of two

#[test]
fn test_abelian_group_under_addition() {
    let rng = &mut rng();
    for _ in 0..100 {
        let a = test_random_polynomial::<i32>(rng, -100..=100);
        let b = test_random_polynomial::<i32>(rng, -100..=100);
        let c = test_random_polynomial::<i32>(rng, -100..=100);

        // additive associativity
        let lhs = (a.clone() + b.clone()) + c.clone();
        let rhs = a.clone() + (b.clone() + c.clone());
        assert_eq!(lhs, rhs);
        // additive commutativity
        let lhs = a.clone() + b.clone();
        let rhs = b.clone() + a.clone();
        assert_eq!(lhs, rhs);
        // additive identity
        let zero = Polynomial::zero();
        let lhs = a.clone() + zero.clone();
        let rhs = a.clone();
        assert_eq!(lhs, rhs);
        // additive inverse
        let lhs = a.clone() + (-a.clone());
        let rhs = zero.clone();
        assert_eq!(lhs, rhs);
    }
}

#[test]
fn test_monoid_under_multiplication() {
    let rng = &mut rng();
    for _ in 0..100 {
        let a = test_random_polynomial::<i32>(rng, -100..=100);
        let b = test_random_polynomial::<i32>(rng, -100..=100);
        let c = test_random_polynomial::<i32>(rng, -100..=100);

        // multiplicative associativity
        let lhs = (a.clone() * b.clone()) * c.clone();
        let rhs = a.clone() * (b.clone() * c.clone());
        assert_eq!(lhs, rhs);
        // multiplicative identity
        let one = Polynomial::one();
        let lhs = a.clone() * one.clone();
        let rhs = a.clone();
        assert_eq!(lhs, rhs);
    }
}

#[test]
fn test_multiplication_distributive_wrt_addition() {
    let rng = &mut rng();
    for _ in 0..100 {
        let a = test_random_polynomial::<i32>(rng, -100..=100);
        let b = test_random_polynomial::<i32>(rng, -100..=100);
        let c = test_random_polynomial::<i32>(rng, -100..=100);

        // left distributivity
        let lhs = a.clone() * (b.clone() + c.clone());
        let rhs = a.clone() * b.clone() + a.clone() * c.clone();
        assert_eq!(lhs, rhs);
        // right distributivity
        let lhs = (a.clone() + b.clone()) * c.clone();
        let rhs = a.clone() * c.clone() + b.clone() * c.clone();
        assert_eq!(lhs, rhs);
    }
}

fn test_random_polynomial<T>(rng: &mut impl Rng, range: RangeInclusive<T>) -> Polynomial<T, N>
where
    T: Zero + Clone + PartialOrd + Ord + SampleUniform,
{
    #[cfg(feature = "rand")]
    {
        use poly_ring_xnp1::rand::CoeffsRangeInclusive;
        let range = CoeffsRangeInclusive::from(range);
        return rng.random_range(range);
    }

    #[cfg(not(feature = "rand"))]
    {
        let coeff_size = rng.random_range(1..N);
        return Polynomial::new(
            (0..coeff_size)
                .map(|_| rng.random_range(range.clone()))
                .collect(),
        );
    }
}
