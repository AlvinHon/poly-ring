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

// /// Natively multiply polynomials `a * b` without modulo.
// pub fn mul<T, const N: usize>(a: &Polynomial<T, N>, b: &Polynomial<T, N>) -> Polynomial<T, N>
// where
//     T: Zero + Clone,
//     for<'a> &'a T: Mul<Output = T> + Add<Output = T>,
// {
//     let mut result = vec![T::zero(); a.coeffs.len() + b.coeffs.len() - 1];
//     for i in 0..a.coeffs.len() {
//         for j in 0..b.coeffs.len() {
//             result[i + j] = &result[i + j] + &(&a.coeffs[i] * &b.coeffs[j]);
//         }
//     }
//     trim_zeros(&mut result);
//     Polynomial { coeffs: result }
// }

/// Negacyclic convolution of two polynomials. i.e. Compute the polynomial
/// `c` = `a` * `b` mod `x^n + 1`, which is in Zp[X]/(x^n + 1).
pub fn negacyclic_convolution<T, const N: usize>(
    a: &Polynomial<T, N>,
    b: &Polynomial<T, N>,
) -> Polynomial<T, N>
where
    T: Zero + Clone,
    for<'a> &'a T: Add<Output = T> + Mul<Output = T> + Sub<Output = T>,
{
    let (a, b) = if a.deg() < b.deg() { (a, b) } else { (b, a) };

    let mut c = Polynomial::new(vec![T::zero(); N]);
    for i in 0..N {
        let a_coeff = a.coefficient(i);
        if a_coeff.is_zero() {
            continue;
        }
        for j in 0..N {
            let b_coeff = b.coefficient(j);
            if b_coeff.is_zero() {
                continue;
            }

            let c_i_j = &c.coeffs[(i + j) % N];
            let pow = (i + j) / N;

            if pow % 2 == 0 {
                c.coeffs[(i + j) % N] = c_i_j + &(&a_coeff * &b_coeff);
            } else {
                c.coeffs[(i + j) % N] = c_i_j - &(&a_coeff * &b_coeff);
            }
        }
    }
    trim_zeros(&mut c.coeffs);
    c
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
fn trim_zeros<T: Zero>(v: &mut Vec<T>) {
    while let Some(&t) = v.last().as_ref() {
        if t.is_zero() {
            v.pop();
        } else {
            break;
        }
    }
}
