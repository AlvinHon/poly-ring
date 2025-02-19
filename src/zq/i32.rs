use core::panic;
use std::ops::{Add, Div, Mul, Neg, Sub};

use num::{Integer, One, Zero};

/// A macro to create a vector of `ZqI32`. It transforms the following code:
///
/// ```ignore
/// zqi32_vec![1,2,3 ; Q]
/// ```
///
/// into
///
/// ```ignore
/// vec![ZqI32::<Q>::new(1), ZqI32::<Q>::new(2), ZqI32::<Q>::new(3)]
/// ```
///
/// Please note the semi-colon `;` is not for specifying the length of the vector (as vec! macro does),
/// but for specifying the value of the prime modulus Q.
#[macro_export]
macro_rules! zqi32_vec {
    ($($x:expr),* ; $Q:expr) => {{
        vec![ $($crate::zq::ZqI32::<$Q>::new($x)),* ]
    }};
}

/// A type representing an element of the ring Z/QZ. The value is normalized to the range \[-Q/2, Q/2\).
///
/// ## Safety
/// Q should be an odd prime number. Although the primality of Q is not checked in the implementation,
/// its implementation makes this assumption for achieving some important properties of ring Z/QZ.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ZqI32<const Q: i32> {
    value: i32,
}

impl<const Q: i32> ZqI32<Q> {
    /// Creates a new `ZqI32` from the given value. It normalizes the value to the range \[-Q/2, Q/2\).
    pub fn new(value: i32) -> Self {
        let a = value.rem_euclid(Q);
        if a > Q / 2 {
            Self { value: a - Q }
        } else {
            Self { value: a }
        }
    }

    fn cast_new(value: i64) -> Self {
        let a = value.rem_euclid(Q as i64) as i32;
        if a > Q / 2 {
            Self { value: a - Q }
        } else {
            Self { value: a }
        }
    }
}

impl<const Q: i32> From<ZqI32<Q>> for i32 {
    fn from(value: ZqI32<Q>) -> Self {
        value.value
    }
}

impl<const Q: i32> From<i32> for ZqI32<Q> {
    fn from(value: i32) -> Self {
        Self::new(value)
    }
}

impl<const Q: i32> Zero for ZqI32<Q> {
    fn zero() -> Self {
        Self { value: 0 }
    }

    fn is_zero(&self) -> bool {
        self.value == 0
    }
}

impl<const Q: i32> One for ZqI32<Q> {
    fn one() -> Self {
        Self { value: 1 }
    }
}

impl<const Q: i32> Neg for ZqI32<Q> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self { value: -self.value }
    }
}

impl<const Q: i32> Neg for &ZqI32<Q> {
    type Output = ZqI32<Q>;

    fn neg(self) -> Self::Output {
        ZqI32 { value: -self.value }
    }
}

impl<const Q: i32> Add for ZqI32<Q> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        match self.value.checked_add(rhs.value) {
            Some(v) => Self::new(v),
            None => Self::cast_new(self.value as i64 + rhs.value as i64),
        }
    }
}

impl<const Q: i32> Add for &ZqI32<Q> {
    type Output = ZqI32<Q>;

    fn add(self, rhs: &ZqI32<Q>) -> Self::Output {
        match self.value.checked_add(rhs.value) {
            Some(v) => ZqI32::new(v),
            None => ZqI32::cast_new(self.value as i64 + rhs.value as i64),
        }
    }
}

impl<const Q: i32> Sub for ZqI32<Q> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        match self.value.checked_sub(rhs.value) {
            Some(v) => Self::new(v),
            None => Self::cast_new(self.value as i64 - rhs.value as i64),
        }
    }
}

impl<const Q: i32> Sub for &ZqI32<Q> {
    type Output = ZqI32<Q>;

    fn sub(self, rhs: &ZqI32<Q>) -> Self::Output {
        match self.value.checked_sub(rhs.value) {
            Some(v) => ZqI32::new(v),
            None => ZqI32::cast_new(self.value as i64 - rhs.value as i64),
        }
    }
}

impl<const Q: i32> Mul for ZqI32<Q> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        match self.value.checked_mul(rhs.value) {
            Some(v) => Self::new(v),
            None => Self::cast_new(self.value as i64 * rhs.value as i64),
        }
    }
}

impl<const Q: i32> Mul for &ZqI32<Q> {
    type Output = ZqI32<Q>;

    fn mul(self, rhs: &ZqI32<Q>) -> Self::Output {
        match self.value.checked_mul(rhs.value) {
            Some(v) => ZqI32::new(v),
            None => ZqI32::cast_new(self.value as i64 * rhs.value as i64),
        }
    }
}

impl<const Q: i32> Div for ZqI32<Q> {
    type Output = ZqI32<Q>;

    fn div(self, rhs: Self) -> Self::Output {
        if rhs.is_zero() {
            panic!("division by zero");
        }
        let x = rhs.value.extended_gcd(&Q).x;
        self.mul(ZqI32::new(x))
    }
}

impl<const Q: i32> Div for &ZqI32<Q> {
    type Output = ZqI32<Q>;

    fn div(self, rhs: &ZqI32<Q>) -> Self::Output {
        if rhs.is_zero() {
            panic!("division by zero");
        }
        let x = rhs.value.extended_gcd(&Q).x;
        self.mul(&ZqI32::new(x))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_zqi32_from() {
        const Q: i32 = 7;

        let a = ZqI32::<Q>::from(10);
        assert_eq!(a.value, 3);

        let b = ZqI32::<Q>::from(-10);
        assert_eq!(b.value, -3);
    }

    #[test]
    fn test_zqi32_add() {
        const Q: i32 = 2147483647;

        let a = ZqI32::<Q>::new(Q / 2);
        let b = ZqI32::<Q>::one();
        let rp = &a + &b;
        let r = a.clone() + b.clone();
        assert_eq!(r, rp);
        assert!(r.value == -Q / 2);
    }

    #[test]
    fn test_zqi32_sub() {
        const Q: i32 = 2147483647;

        let a = ZqI32::<Q>::new(-Q / 2);
        let b = ZqI32::<Q>::one();
        let rp = &a - &b;
        let r = a.clone() - b.clone();
        assert_eq!(r, rp);
        assert!(r.value == Q / 2);
    }

    #[test]
    fn test_zqi32_add_sub() {
        const Q: i32 = 7;

        // check all permutations of [-3,-2,-1,0,1,2,3]
        for i in -3..=3 {
            for j in -3..=3 {
                let a = ZqI32::<Q>::new(i);
                let b = ZqI32::<Q>::new(j);
                let c = &a + &b;

                assert_eq!(&c - &a, b.clone());
                assert_eq!(&c - &b, a.clone());
            }
        }
    }

    #[test]
    fn test_zqi32_mul() {
        const Q: i32 = 7;

        // [-3,-2,-1,0,1,2,3] <-> [4,5,6,0,1,2,3]
        let a = ZqI32::<Q>::new(-3);
        let b = ZqI32::<Q>::new(-2);
        let rp = &a * &b;
        let r = a.clone() * b.clone();
        assert_eq!(r, rp);
        // -3 * -2 = 6 = -1 mod 7
        assert!(r.value == -1);
    }

    #[test]
    fn test_zqi32_mul_overflow() {
        const Q: i32 = 2147483647;

        let a = ZqI32::<Q>::new(Q / 2);
        let b = ZqI32::<Q>::new(Q / 2);
        let rp = &a * &b;
        let r = a.clone() * b.clone();
        assert_eq!(r, rp);
        assert!(r.value <= Q / 2);
    }

    #[test]
    fn test_zqi32_div() {
        const Q: i32 = 7;

        // [-3,-2,-1,0,1,2,3] <-> [4,5,6,0,1,2,3]
        // we had -3 * -2 = 6 = -1 mod 7, so -1 / -2 = -3 mod 7
        let a = ZqI32::<Q>::new(-1);
        let b = ZqI32::<Q>::new(-2);
        let rp = &a / &b;
        let r = a.clone() / b.clone();
        assert_eq!(r, rp);
        assert_eq!(r.value, -3);
    }

    #[test]
    #[should_panic]
    fn test_zqi32_div_zero() {
        const Q: i32 = 7;

        let a = ZqI32::<Q>::one();
        let b = ZqI32::<Q>::zero();
        let _ = &a / &b;
    }

    #[test]
    fn test_zqi32_mui_div() {
        const Q: i32 = 7;

        // check all permutations of [-3,-2,-1,0,1,2,3]
        for i in -3..=3 {
            for j in -3..=3 {
                let a = ZqI32::<Q>::new(i);
                let b = ZqI32::<Q>::new(j);
                let c = &a * &b;

                if b.is_zero() {
                    continue;
                }

                if a.is_zero() {
                    assert!(c.is_zero());
                    continue;
                }

                assert_eq!(&c / &b, a.clone());
                assert_eq!(&c / &a, b.clone(),);
            }
        }
    }

    #[test]
    fn test_zqi32_vec() {
        let v = zqi32_vec![-9, -6, 0, 6; 7];
        let values = v.iter().map(|x| x.value).collect::<Vec<_>>();
        assert_eq!(values, vec![-2, 1, 0, -1]);
    }
}
