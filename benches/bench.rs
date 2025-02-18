use criterion::{criterion_main, Criterion};
use rand::{rng, Rng};

criterion_main!(benches);

pub fn benches() {
    let c = &mut Criterion::default().configure_from_args();

    // bench methods:
    bench_polynomial_ring_multiplication(c);
    bench_polynomial_ring_addition(c);

    // bench methods for feature "zq"
    #[cfg(feature = "zq")]
    {
        bench_polynomial_ring_addition_over_zq(c);
        bench_polynomial_ring_multiplication_over_zq(c);
    }
}

const N: usize = 512; // power of two

pub fn bench_polynomial_ring_multiplication(c: &mut Criterion) {
    let rng = &mut rng();
    let p_coeffs = (0..N)
        .map(|_| rng.random_range(-100..100))
        .collect::<Vec<_>>();
    let q_coeffs = (0..N)
        .map(|_| rng.random_range(-100..100))
        .collect::<Vec<_>>();

    let mut group = c.benchmark_group("Polynomial Ring Multiplication");

    // this crate
    let p = poly_ring_xnp1::Polynomial::<i32, N>::new(p_coeffs.clone());
    let q = poly_ring_xnp1::Polynomial::<_, N>::new(q_coeffs.clone());

    group.bench_function("poly_ring_xnp1", |b| {
        b.iter_batched(
            || (p.clone(), q.clone()),
            |(p, q)| {
                let _ = p * q;
            },
            criterion::BatchSize::SmallInput,
        );
    });

    // crate: polynomial_ring
    let p = polynomial_ring::Polynomial::new(p_coeffs);
    let q = polynomial_ring::Polynomial::new(q_coeffs);
    let modulo = {
        // x^n + 1
        let mut m_coeffs = vec![0; N + 1];
        m_coeffs[0] = 1;
        m_coeffs[N] = 1;
        polynomial_ring::Polynomial::new(m_coeffs)
    };

    group.bench_function("polynomial_ring", |b| {
        b.iter(|| {
            let _ = (&p * &q).division(&modulo);
        })
    });
}

pub fn bench_polynomial_ring_addition(c: &mut Criterion) {
    let rng = &mut rng();
    let p_coeffs = (0..N)
        .map(|_| rng.random_range(-100..100))
        .collect::<Vec<_>>();
    let q_coeffs = (0..N)
        .map(|_| rng.random_range(-100..100))
        .collect::<Vec<_>>();

    let mut group = c.benchmark_group("Polynomial Ring Addition");

    // this crate
    let p = poly_ring_xnp1::Polynomial::<i32, N>::new(p_coeffs.clone());
    let q = poly_ring_xnp1::Polynomial::<_, N>::new(q_coeffs.clone());

    group.bench_function("poly_ring_xnp1", |b| {
        b.iter_batched(
            || (p.clone(), q.clone()),
            |(p, q)| {
                let _ = p + q;
            },
            criterion::BatchSize::SmallInput,
        );
    });

    // crate: polynomial_ring
    let p = polynomial_ring::Polynomial::new(p_coeffs);
    let q = polynomial_ring::Polynomial::new(q_coeffs);
    let modulo = {
        // x^n + 1
        let mut m_coeffs = vec![0; N + 1];
        m_coeffs[0] = 1;
        m_coeffs[N] = 1;
        polynomial_ring::Polynomial::new(m_coeffs)
    };

    group.bench_function("polynomial_ring", |b| {
        b.iter(|| {
            let _ = (&p + &q).division(&modulo);
        })
    });
}

#[cfg(feature = "zq")]
fn bench_polynomial_ring_addition_over_zq(c: &mut Criterion) {
    use abstalg::{CommuntativeMonoid, PolynomialAlgebra, QuotientField, QuotientRing, I32};

    let rng = &mut rng();

    const Q: u32 = 7;

    let p_coeffs = (0..N)
        .map(|_| rng.random_range(0..7u32))
        .collect::<Vec<_>>();
    let q_coeffs = (0..N)
        .map(|_| rng.random_range(0..7u32))
        .collect::<Vec<_>>();

    let mut group = c.benchmark_group("Polynomial Ring Addition Over Zq");

    // this crate
    let p = poly_ring_xnp1::Polynomial::<poly_ring_xnp1::zq::ZqU32<Q>, N>::new(p_coeffs.clone());
    let q = poly_ring_xnp1::Polynomial::<_, N>::new(q_coeffs.clone());

    group.bench_function("poly_ring_xnp1", |b| {
        b.iter_batched(
            || (p.clone(), q.clone()),
            |(p, q)| {
                let _ = p + q;
            },
            criterion::BatchSize::SmallInput,
        );
    });

    // crate: abstalg
    let p_coeffs = p_coeffs.into_iter().map(|x| x as i32).collect::<Vec<_>>();
    let q_coeffs = q_coeffs.into_iter().map(|x| x as i32).collect::<Vec<_>>();

    let poly_ring = {
        let field = QuotientField::new(I32, Q as i32);
        let ring = PolynomialAlgebra::new(field);
        let moduli = (0..=N)
            .map(|i| if i == 0 || i == N { 1 } else { 0 })
            .collect::<Vec<_>>();
        QuotientRing::new(ring, moduli)
    };

    group.bench_function("abstalg", |b| {
        b.iter(|| {
            let _ = poly_ring.add(&p_coeffs, &q_coeffs);
        })
    });
}

#[cfg(feature = "zq")]
fn bench_polynomial_ring_multiplication_over_zq(c: &mut Criterion) {
    use abstalg::{PolynomialAlgebra, QuotientField, QuotientRing, Semigroup, I32};

    let rng = &mut rng();

    const Q: u32 = 7;

    let p_coeffs = (0..N)
        .map(|_| rng.random_range(0..7u32))
        .collect::<Vec<_>>();
    let q_coeffs = (0..N)
        .map(|_| rng.random_range(0..7u32))
        .collect::<Vec<_>>();

    let mut group = c.benchmark_group("Polynomial Ring Multiplication Over Zq");

    // this crate
    let p = poly_ring_xnp1::Polynomial::<poly_ring_xnp1::zq::ZqU32<Q>, N>::new(p_coeffs.clone());
    let q = poly_ring_xnp1::Polynomial::<_, N>::new(q_coeffs.clone());

    group.bench_function("poly_ring_xnp1", |b| {
        b.iter_batched(
            || (p.clone(), q.clone()),
            |(p, q)| {
                let _ = p * q;
            },
            criterion::BatchSize::SmallInput,
        );
    });

    // crate: abstalg
    let p_coeffs = p_coeffs.into_iter().map(|x| x as i32).collect::<Vec<_>>();
    let q_coeffs = q_coeffs.into_iter().map(|x| x as i32).collect::<Vec<_>>();

    let poly_ring = {
        let field = QuotientField::new(I32, Q as i32);
        let ring = PolynomialAlgebra::new(field);
        let moduli = (0..=N)
            .map(|i| if i == 0 || i == N { 1 } else { 0 })
            .collect::<Vec<_>>();
        QuotientRing::new(ring, moduli)
    };

    group.bench_function("abstalg", |b| {
        b.iter(|| {
            let _ = poly_ring.mul(&p_coeffs, &q_coeffs);
        })
    });
}
