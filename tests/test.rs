use num::{One, Zero};
use poly_ring_xnp1::Polynomial;
use rand::{
    distr::uniform::{SampleRange, SampleUniform},
    rng, Rng,
};

const N: usize = 512; // power of two

#[test]
fn test_abelian_group_under_addition() {
    let rng = &mut rng();
    for _ in 0..100 {
        let a = rand_polynomial::<N, _, _, _>(rng, -100..100);
        let b = rand_polynomial::<N, _, _, _>(rng, -100..100);
        let c = rand_polynomial::<N, _, _, _>(rng, -100..100);

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
        let a = rand_polynomial::<N, _, _, _>(rng, -100..100);
        let b = rand_polynomial::<N, _, _, _>(rng, -100..100);
        let c = rand_polynomial::<N, _, _, _>(rng, -100..100);

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
        let a = rand_polynomial::<N, _, _, _>(rng, -100..100);
        let b = rand_polynomial::<N, _, _, _>(rng, -100..100);
        let c = rand_polynomial::<N, _, _, _>(rng, -100..100);

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

fn rand_polynomial<const N: usize, T, R, G>(rng: &mut R, range: G) -> Polynomial<T, N>
where
    T: SampleUniform + Zero,
    R: Rng,
    G: SampleRange<T> + Clone,
{
    let coeff_size = rng.random_range(1..N);
    Polynomial::new(
        (0..coeff_size)
            .map(|_| rng.random_range(range.clone()))
            .collect(),
    )
}
