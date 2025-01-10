use criterion::{criterion_group, criterion_main, Criterion};
use rand::Rng;

criterion_group!(benches, bench_polynomial_ring_multiplication);

criterion_main!(benches);

const N: usize = 512; // power of two

pub fn bench_polynomial_ring_multiplication(c: &mut Criterion) {
    let rng = &mut rand::thread_rng();
    let p_coeffs = (0..N).map(|_| rng.gen_range(-100..100)).collect::<Vec<_>>();
    let q_coeffs = (0..N).map(|_| rng.gen_range(-100..100)).collect::<Vec<_>>();

    let mut group = c.benchmark_group("Polynomial Ring Multiplication");

    // this crate
    let p = poly_ring::Polynomial::<_, N>::new(p_coeffs.clone());
    let q = poly_ring::Polynomial::<_, N>::new(q_coeffs.clone());

    group.bench_function("poly_ring", |b| {
        b.iter(|| {
            let _ = p.clone() * q.clone();
        })
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
