use std::ops::{Add, Mul, Sub};

use num::{One, Zero};

use crate::{modulo::PolynomialModulo, Polynomial};

/// Add polynomials `a + b` without modulo.
pub fn add<T, const N: usize>(a: &Polynomial<T, N>, b: &Polynomial<T, N>) -> Polynomial<T, N>
where
    T: Zero + Clone,
    for<'a> &'a T: Add<Output = T>,
{
    let mut result = vec![T::zero(); std::cmp::max(a.coeffs.len(), b.coeffs.len())];
    for (i, r_i) in result.iter_mut().enumerate() {
        if i < a.coeffs.len() {
            *r_i = &*r_i + &a.coeffs[i];
        }
        if i < b.coeffs.len() {
            *r_i = &*r_i + &b.coeffs[i];
        }
    }
    trim_zeros(&mut result);
    Polynomial { coeffs: result }
}

/// Multiply polynomials `a * b` with modulo x^n + 1 by using toeplitz matrix-vector multiplication.
pub(crate) fn cyclic_mul<T, const N: usize>(
    a: &Polynomial<T, N>,
    b: &Polynomial<T, N>,
) -> Polynomial<T, N>
where
    T: Zero + Clone,
    for<'a> &'a T: Add<Output = T> + Mul<Output = T> + Sub<Output = T>,
{
    // toeplitz matrix-vector multiplication
    let mut result = vec![T::zero(); N];
    for (i, result_i) in result.iter_mut().enumerate() {
        for j in 0..N {
            // only consider non-zero coefficients
            if let Some(b_coeff) = b.coeffs.get(j) {
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
                if i >= j {
                    if let Some(a_coeff) = a.coeffs.get(i - j) {
                        *result_i = &*result_i + &(a_coeff * b_coeff);
                    }
                } else if let Some(a_coeff) = a.coeffs.get(N - j + i) {
                    *result_i = &*result_i - &(a_coeff * b_coeff);
                }
            }
        }
    }
    trim_zeros(&mut result);
    Polynomial { coeffs: result }
}

/// Computes the pseudo remainder `r` of this polynomial `p` by another polynomial modulo.
/// i.e. `r = p - q * d` where `q` is the quotient of the division.
pub fn modulo<T, const N: usize>(
    p: &Polynomial<T, N>,
    modulo: &PolynomialModulo<T, N>,
) -> Polynomial<T, N>
where
    T: Zero + One + Clone,
    for<'a> &'a T: Mul<Output = T> + Sub<Output = T> + Add<Output = T>,
{
    if p.is_zero() {
        return Polynomial::zero();
    }

    if p.deg() < modulo.deg() {
        return p.clone();
    }

    // Polynomial Pseudo-Division (Wu's method, https://en.wikipedia.org/wiki/Wu%27s_method_of_characteristic_set)
    // Variable names are using the notations from the reference: https://aszanto.math.ncsu.edu/MA722/ln-02.pdf
    let mut r = p.clone(); // r = f
    let s = modulo.deg();
    let b_s = modulo.leading_coefficient();
    while !r.is_zero() && r.deg() >= s {
        // deg_y(r) - s
        let pow_y = r.deg() - s;
        let lc_r = r.coeffs.last().cloned().unwrap();
        // r' = b_s r - lc_r * g * x^pow_y
        for i in 0..r.deg() {
            let term: T = if i < pow_y {
                T::zero()
            } else {
                &lc_r * &modulo.coefficient(i - pow_y)
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
        let r = add(&p1, &p2);
        assert_eq!(r.coeffs, vec![5, 7, 3]);

        let p1 = Polynomial::<i32, N>::new(vec![2, 1]);
        let p2 = Polynomial::new(vec![5, 4, 3]);
        let r = add(&p1, &p2);
        assert_eq!(r.coeffs, vec![7, 5, 3]);

        let p1 = Polynomial::<i32, N>::new(vec![1, 2, 3]);
        let p2 = Polynomial::zero();
        let r = add(&p1, &p2);
        assert_eq!(r.coeffs, vec![1, 2, 3]);

        let p1 = Polynomial::<i32, N>::zero();
        let p2 = Polynomial::new(vec![1, 2, 3]);
        let r = add(&p1, &p2);
        assert_eq!(r.coeffs, vec![1, 2, 3]);
    }

    #[test]
    fn test_neg() {
        let p1 = Polynomial::<i32, N>::new(vec![1, 2, 3]);
        let p2 = Polynomial::new(vec![4, 5]);
        let r = add(&p1, &p2.neg());
        assert_eq!(r.coeffs, vec![-3, -3, 3]);

        let p1 = Polynomial::<i32, N>::new(vec![2, 1]);
        let p2 = Polynomial::new(vec![5, 4, 3]);
        let r = add(&p1, &p2.neg());
        assert_eq!(r.coeffs, vec![-3, -3, -3]);

        let p1 = Polynomial::<i32, N>::new(vec![1, 2, 3]);
        let p2 = Polynomial::zero();
        let r = add(&p1, &p2.neg());
        assert_eq!(r.coeffs, vec![1, 2, 3]);

        let p1 = Polynomial::<i32, N>::zero();
        let p2 = Polynomial::new(vec![1, 2, 3]);
        let r = add(&p1, &p2.neg());
        assert_eq!(r.coeffs, vec![-1, -2, -3]);
    }

    #[test]
    fn test_cyclic_mul() {
        let rng = &mut rand::thread_rng();
        let a =
            Polynomial::<i32, N>::new((0..N).map(|_| rng.gen_range(0..100)).collect::<Vec<_>>());

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
