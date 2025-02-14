use std::ops::{Add, Mul, Sub};

use num::{One, Zero};

use crate::{modulo::PolynomialModulus, Polynomial};

/// Add polynomials `a + b` without modulo.
pub(crate) fn add<T, const N: usize>(a: Polynomial<T, N>, b: Polynomial<T, N>) -> Polynomial<T, N>
where
    T: Zero,
    for<'a> &'a T: Add<Output = T>,
{
    let (a, b) = if a.coeffs.len() < b.coeffs.len() {
        (b, a)
    } else {
        (a, b)
    };
    let mut coeffs = a.coeffs;
    coeffs
        .iter_mut()
        .zip(b.coeffs.iter())
        .for_each(|(a_i, b_i)| {
            *a_i = &*a_i + b_i;
        });
    trim_zeros(&mut coeffs);
    Polynomial { coeffs }
}

/// Multiply polynomials `a * b` with modulo x^n + 1 by using toeplitz matrix-vector multiplication.
#[allow(clippy::needless_range_loop)] // allow for better performance
pub(crate) fn cyclic_mul<T, const N: usize>(
    a: &Polynomial<T, N>,
    b: &Polynomial<T, N>,
) -> Polynomial<T, N>
where
    T: Zero + Clone,
    for<'a> &'a T: Add<Output = T> + Mul<Output = T> + Sub<Output = T>,
{
    // toeplitz matrix-vector multiplication
    let mut coeffs = vec![T::zero(); N];

    // only consider non-zero coefficients
    for j in 0..b.coeffs.len() {
        let b_coeff = &b.coeffs[j];

        // Here computes the coefficient of Toeplitz matrix from the
        // polynomial `a` at `(i, j)` under ring Z[x]/(x^n + 1).
        // The Toeplitz matrix is in form (e.g. N = 4):
        //
        // [a_0, -a_3, -a_2, -a_1]
        // [a_1, a_0, -a_3, -a_2]
        // [a_2, a_1, a_0, -a_3]
        // [a_3, a_2, a_1, a_0]
        //
        // and then apply the matrix-vector multiplication.

        // case i < j
        for i in 0..j {
            if let Some(a_coeff) = a.coeffs.get(N - j + i) {
                coeffs[i] = &coeffs[i] - &(a_coeff * b_coeff);
            } else {
                break;
            }
        }

        // case i >= j
        for i in j..N {
            if let Some(a_coeff) = a.coeffs.get(i - j) {
                coeffs[i] = &coeffs[i] + &(a_coeff * b_coeff);
            } else {
                break;
            }
        }
    }
    trim_zeros(&mut coeffs);
    Polynomial { coeffs }
}

/// Computes the pseudo remainder `r` of this polynomial `p` by another polynomial modulo.
/// i.e. `r = p - q * d` where `q` is the quotient of the division.
/// Note that it only works for monic modulus (i.e. leading coefficient is 1).
pub(crate) fn modulo<T, const N: usize>(
    p: Polynomial<T, N>,
    modulus: PolynomialModulus<T>,
) -> Polynomial<T, N>
where
    T: Zero + One + Clone,
    for<'a> &'a T: Mul<Output = T> + Sub<Output = T> + Add<Output = T>,
{
    if p.is_zero() {
        return Polynomial::zero();
    }

    if p.deg() < modulus.deg() {
        return p;
    }

    // Polynomial Pseudo-Division (Wu's method, https://en.wikipedia.org/wiki/Wu%27s_method_of_characteristic_set)
    // Variable names are using the notations from the reference: https://aszanto.math.ncsu.edu/MA722/ln-02.pdf
    let mut r = p; // r = f
    let s = modulus.deg();
    let b_s = modulus.leading_coefficient();
    while !r.is_zero() && r.deg() >= s {
        // deg_y(r) - s
        let pow_y = r.deg() - s;
        let lc_r = r.coeffs.last().cloned().unwrap();
        // r' = b_s r - lc_r * g * x^pow_y
        for i in 0..r.deg() {
            let term: T = if i < pow_y {
                T::zero()
            } else {
                &lc_r * &modulus.coefficient(i - pow_y)
            };
            r.coeffs[i] = &(&b_s * &r.coeffs[i]) - &term;
        }
        r.coeffs.pop();
        trim_zeros(&mut r.coeffs);
    }

    r
}

/// Trims the leading zero coefficients of the polynomial.
pub(crate) fn trim_zeros<T: Zero>(v: &mut Vec<T>) {
    while let Some(&t) = v.last().as_ref() {
        if t.is_zero() {
            v.pop();
        } else {
            break;
        }
    }
}

#[cfg(test)]
mod tests {
    use std::ops::Neg;

    use rand::Rng;

    use super::*;

    const N: usize = 512; // power of two

    #[test]
    fn test_add() {
        let p1 = Polynomial::<i32, N>::new(vec![1, 2, 3]);
        let p2 = Polynomial::new(vec![4, 5]);
        let r = add(p1, p2);
        assert_eq!(r.coeffs, vec![5, 7, 3]);

        let p1 = Polynomial::<i32, N>::new(vec![2, 1]);
        let p2 = Polynomial::new(vec![5, 4, 3]);
        let r = add(p1, p2);
        assert_eq!(r.coeffs, vec![7, 5, 3]);

        let p1 = Polynomial::<i32, N>::new(vec![1, 2, 3]);
        let p2 = Polynomial::zero();
        let r = add(p1, p2);
        assert_eq!(r.coeffs, vec![1, 2, 3]);

        let p1 = Polynomial::<i32, N>::zero();
        let p2 = Polynomial::new(vec![1, 2, 3]);
        let r = add(p1, p2);
        assert_eq!(r.coeffs, vec![1, 2, 3]);
    }

    #[test]
    fn test_neg() {
        let p1 = Polynomial::<i32, N>::new(vec![1, 2, 3]);
        let p2 = Polynomial::new(vec![4, 5]);
        let r = add(p1, p2.neg());
        assert_eq!(r.coeffs, vec![-3, -3, 3]);

        let p1 = Polynomial::<i32, N>::new(vec![2, 1]);
        let p2 = Polynomial::new(vec![5, 4, 3]);
        let r = add(p1, p2.neg());
        assert_eq!(r.coeffs, vec![-3, -3, -3]);

        let p1 = Polynomial::<i32, N>::new(vec![1, 2, 3]);
        let p2 = Polynomial::zero();
        let r = add(p1, p2.neg());
        assert_eq!(r.coeffs, vec![1, 2, 3]);

        let p1 = Polynomial::<i32, N>::zero();
        let p2 = Polynomial::new(vec![1, 2, 3]);
        let r = add(p1, p2.neg());
        assert_eq!(r.coeffs, vec![-1, -2, -3]);
    }

    #[test]
    fn test_cyclic_mul() {
        let rng = &mut rand::rng();
        let a =
            Polynomial::<i32, N>::new((0..N).map(|_| rng.random_range(0..100)).collect::<Vec<_>>());

        let p = Polynomial::<i32, N>::new(vec![0, 1]);
        let rhs = cyclic_mul(&a, &p);

        // (x^n + 1)-cyclic lattice is an ideal in Z[x]/(x^n + 1)
        // (v_{0} + ... v_{n-2} x^{n-2} + v_{n-1} x^{n-1}) x = -v_{n-1} + v_{0} x + ... + v_{n-2} x^{n-1}
        assert!(a.coeffs[N - 1] == -&rhs.coeffs[0]);
        for i in 0..N - 1 {
            assert!(a.coeffs[i] == rhs.coeffs[i + 1]);
        }
    }
}
