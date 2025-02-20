use std::ops::{Add, Div, Mul, Neg, Sub};

use num::{traits::Inv, Integer, One, Zero};

/// A macro to create a vector of `ZqI64`. It transforms the following code:
///
/// ```ignore
/// zqi64_vec![1,2,3 ; Q]
/// ```
///
/// into
///
/// ```ignore
/// vec![ZqI64::<Q>::new(1), ZqI64::<Q>::new(2), ZqI64::<Q>::new(3)]
/// ```
///
/// Please note the semi-colon `;` is not for specifying the length of the vector (as vec! macro does),
/// but for specifying the value of the prime modulus Q.
#[macro_export]
macro_rules! zqi64_vec {
    ($($x:expr),* ; $Q:expr) => {{
        vec![ $($crate::zq::ZqI64::<$Q>::new($x)),* ]
    }};
}

/// A type representing an element of the ring Z/QZ. The value is normalized to the range \[-Q/2, Q/2\).
///
/// ## Safety
/// Q should be an odd prime number. Although the primality of Q is not checked in the implementation,
/// its implementation makes this assumption for achieving some important properties of ring Z/QZ.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ZqI64<const Q: i64> {
    value: i64,
}

impl<const Q: i64> ZqI64<Q> {
    /// Creates a new `ZqI64` from the given value. It normalizes the value to the range \[-Q/2, Q/2\).
    pub fn new(value: i64) -> Self {
        let a = value.rem_euclid(Q);
        if a > Q / 2 {
            Self { value: a - Q }
        } else {
            Self { value: a }
        }
    }

    fn cast_new(value: i128) -> Self {
        let a = value.rem_euclid(Q as i128) as i64;
        if a > Q / 2 {
            Self { value: a - Q }
        } else {
            Self { value: a }
        }
    }
}

impl<const Q: i64> From<ZqI64<Q>> for i64 {
    fn from(value: ZqI64<Q>) -> Self {
        value.value
    }
}

impl<const Q: i64> From<i32> for ZqI64<Q> {
    fn from(value: i32) -> Self {
        Self::new(value as i64)
    }
}

impl<const Q: i64> From<i64> for ZqI64<Q> {
    fn from(value: i64) -> Self {
        Self::new(value)
    }
}

impl<const Q: i64> Zero for ZqI64<Q> {
    fn zero() -> Self {
        Self { value: 0 }
    }

    fn is_zero(&self) -> bool {
        self.value == 0
    }
}

impl<const Q: i64> One for ZqI64<Q> {
    fn one() -> Self {
        Self { value: 1 }
    }
}

impl<const Q: i64> Neg for ZqI64<Q> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self { value: -self.value }
    }
}

impl<const Q: i64> Neg for &ZqI64<Q> {
    type Output = ZqI64<Q>;

    fn neg(self) -> Self::Output {
        ZqI64 { value: -self.value }
    }
}

impl<const Q: i64> Add for ZqI64<Q> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        match self.value.checked_add(rhs.value) {
            Some(v) => Self::new(v),
            None => Self::cast_new(self.value as i128 + rhs.value as i128),
        }
    }
}

impl<const Q: i64> Add for &ZqI64<Q> {
    type Output = ZqI64<Q>;

    fn add(self, rhs: &ZqI64<Q>) -> Self::Output {
        match self.value.checked_add(rhs.value) {
            Some(v) => ZqI64::new(v),
            None => ZqI64::cast_new(self.value as i128 + rhs.value as i128),
        }
    }
}

impl<const Q: i64> Sub for ZqI64<Q> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        match self.value.checked_sub(rhs.value) {
            Some(v) => Self::new(v),
            None => Self::cast_new(self.value as i128 - rhs.value as i128),
        }
    }
}

impl<const Q: i64> Sub for &ZqI64<Q> {
    type Output = ZqI64<Q>;

    fn sub(self, rhs: &ZqI64<Q>) -> Self::Output {
        match self.value.checked_sub(rhs.value) {
            Some(v) => ZqI64::new(v),
            None => ZqI64::cast_new(self.value as i128 - rhs.value as i128),
        }
    }
}

impl<const Q: i64> Mul for ZqI64<Q> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        match self.value.checked_mul(rhs.value) {
            Some(v) => Self::new(v),
            None => Self::cast_new(self.value as i128 * rhs.value as i128),
        }
    }
}

impl<const Q: i64> Mul for &ZqI64<Q> {
    type Output = ZqI64<Q>;

    fn mul(self, rhs: &ZqI64<Q>) -> Self::Output {
        match self.value.checked_mul(rhs.value) {
            Some(v) => ZqI64::new(v),
            None => ZqI64::cast_new(self.value as i128 * rhs.value as i128),
        }
    }
}

impl<const Q: i64> Div for ZqI64<Q> {
    type Output = ZqI64<Q>;

    fn div(self, rhs: Self) -> Self::Output {
        if rhs.is_zero() {
            panic!("division by zero");
        }
        let x = rhs.value.extended_gcd(&Q).x;
        self.mul(ZqI64::new(x))
    }
}

impl<const Q: i64> Div for &ZqI64<Q> {
    type Output = ZqI64<Q>;

    fn div(self, rhs: &ZqI64<Q>) -> Self::Output {
        if rhs.is_zero() {
            panic!("division by zero");
        }
        let x = rhs.value.extended_gcd(&Q).x;
        self.mul(&ZqI64::new(x))
    }
}

impl<const Q: i64> Inv for ZqI64<Q> {
    type Output = Self;

    fn inv(self) -> Self::Output {
        if self.is_zero() {
            panic!("division by zero");
        }
        let x = self.value.extended_gcd(&Q).x;
        ZqI64::new(x)
    }
}

impl<const Q: i64> Inv for &ZqI64<Q> {
    type Output = ZqI64<Q>;

    fn inv(self) -> Self::Output {
        if self.is_zero() {
            panic!("division by zero");
        }
        let x = self.value.extended_gcd(&Q).x;
        ZqI64::new(x)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_zqi64_from() {
        const Q: i64 = 7;

        let a = ZqI64::<Q>::from(10i64);
        assert_eq!(a.value, 3);

        let b = ZqI64::<Q>::from(-10i32);
        assert_eq!(b.value, -3);
    }

    #[test]
    fn test_zqi64_add() {
        const Q: i64 = 416608695821;

        let a = ZqI64::<Q>::new(Q / 2);
        let b = ZqI64::<Q>::one();
        let rp = &a + &b;
        let r = a.clone() + b.clone();
        assert_eq!(r, rp);
        assert!(r.value == -Q / 2);
    }

    #[test]
    fn test_zqi64_sub() {
        const Q: i64 = 416608695821;

        let a = ZqI64::<Q>::new(-Q / 2);
        let b = ZqI64::<Q>::one();
        let rp = &a - &b;
        let r = a.clone() - b.clone();
        assert_eq!(r, rp);
        assert!(r.value == Q / 2);
    }

    #[test]
    fn test_zqi64_add_sub() {
        const Q: i64 = 7;

        // check all permutations of [-3,-2,-1,0,1,2,3]
        for i in -3..=3 {
            for j in -3..=3 {
                let a = ZqI64::<Q>::new(i);
                let b = ZqI64::<Q>::new(j);
                let c = &a + &b;

                assert_eq!(&c - &a, b.clone());
                assert_eq!(&c - &b, a.clone());
            }
        }
    }

    #[test]
    fn test_zqi64_mul() {
        const Q: i64 = 7;

        // [-3,-2,-1,0,1,2,3] <-> [4,5,6,0,1,2,3]
        let a = ZqI64::<Q>::new(-3);
        let b = ZqI64::<Q>::new(-2);
        let rp = &a * &b;
        let r = a.clone() * b.clone();
        assert_eq!(r, rp);
        // -3 * -2 = 6 = -1 mod 7
        assert!(r.value == -1);
    }

    #[test]
    fn test_zqi64_mul_overflow() {
        const Q: i64 = 416608695821;

        let a = ZqI64::<Q>::new(Q / 2);
        let b = ZqI64::<Q>::new(Q / 2);
        let rp = &a * &b;
        let r = a.clone() * b.clone();
        assert_eq!(r, rp);
        assert!(r.value <= Q / 2);
    }

    #[test]
    fn test_zqi64_div() {
        const Q: i64 = 7;

        // [-3,-2,-1,0,1,2,3] <-> [4,5,6,0,1,2,3]
        // we had -3 * -2 = 6 = -1 mod 7, so -1 / -2 = -3 mod 7
        let a = ZqI64::<Q>::new(-1);
        let b = ZqI64::<Q>::new(-2);
        let rp = &a / &b;
        let r = a.clone() / b.clone();
        assert_eq!(r, rp);
        assert_eq!(r.value, -3);
    }

    #[test]
    #[should_panic]
    fn test_zqi64_div_zero() {
        const Q: i64 = 7;

        let a = ZqI64::<Q>::one();
        let b = ZqI64::<Q>::zero();
        let _ = &a / &b;
    }

    #[test]
    fn test_zqi64_inv() {
        const Q: i64 = 7;

        // [-3,-2,-1,0,1,2,3] <-> [4,5,6,0,1,2,3]
        // 2 * -3 = -6 = 1 mod 7, so 2^-1 = -3 mod 7
        let a = ZqI64::<Q>::new(2);
        let rp = (&a).inv();
        let r = a.clone().inv();
        assert_eq!(r, rp);
        assert_eq!(r.value, -3);
    }

    #[test]
    fn test_zqi64_mui_div() {
        const Q: i64 = 7;

        // check all permutations of [-3,-2,-1,0,1,2,3]
        for i in -3..=3 {
            for j in -3..=3 {
                let a = ZqI64::<Q>::new(i);
                let b = ZqI64::<Q>::new(j);
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
    fn test_zqi64_vec() {
        let v = zqi64_vec![-9, -6, 0, 6; 7];
        let values = v.iter().map(|x| x.value).collect::<Vec<_>>();
        assert_eq!(values, vec![-2, 1, 0, -1]);
    }
}
