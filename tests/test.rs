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

#[cfg(feature = "serde")]
#[test]
fn test_serde() {
    let p = Polynomial::<i32, 4>::new(vec![1, 2, 3, 4]);
    let serialized_p = bincode::serialize(&p).unwrap();
    // - 8 bytes for length of the coefficients in bincode
    // - 4 bytes for each i32 coefficient
    // => 8 + 4 * 4 = 24
    assert_eq!(serialized_p.len(), 24);

    let deserialized_p = bincode::deserialize(&serialized_p).unwrap();
    assert_eq!(p, deserialized_p);

    let p = Polynomial::<i64, 4>::new(vec![1, 2, 3, 4]);
    let serialized_p = bincode::serialize(&p).unwrap();
    // - 8 bytes for length of the coefficients in bincode
    // - 8 bytes for each i64 coefficient
    // => 8 + 8 * 4 = 40
    assert_eq!(serialized_p.len(), 40);

    let deserialized_p = bincode::deserialize(&serialized_p).unwrap();
    assert_eq!(p, deserialized_p);
}

#[cfg(all(feature = "zq", feature = "serde"))]
#[test]
fn test_serde_over_zq() {
    use poly_ring_xnp1::zq::{ZqI32, ZqI64};
    let p = Polynomial::<ZqI32<7>, 4>::new(vec![-1, -2, 1, 2]);
    let serialized_p = bincode::serialize(&p).unwrap();
    // - 8 bytes for length of the coefficients in bincode
    // - 4 bytes for each ZqI32 coefficient (it only contains a i32 value)
    // => 8 + 4 * 4 = 24
    assert_eq!(serialized_p.len(), 24);

    let p = Polynomial::<ZqI64<7>, 4>::new(vec![-1, -2, 1, 2]);
    let serialized_p = bincode::serialize(&p).unwrap();
    // - 8 bytes for length of the coefficients in bincode
    // - 8 bytes for each ZqI64 coefficient (it only contains a i64 value)
    // => 8 + 8 * 4 = 40
    assert_eq!(serialized_p.len(), 40);
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
