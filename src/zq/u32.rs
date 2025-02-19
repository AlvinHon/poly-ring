use std::ops::{Add, Div, Mul, Neg, Sub};

use num::{Integer, One, Zero};

/// A macro to create a vector of `ZqU32`. It transforms the following code:
///
/// ```ignore
/// zqu32_vec![1,2,3 ; Q]
/// ```
///
/// into
///
/// ```ignore
/// vec![ZqU32::<Q>::new(1), ZqU32::<Q>::new(2), ZqU32::<Q>::new(3)]
/// ```
///
/// Please note the semi-colon `;` is not for specifying the length of the vector (as vec! macro does),
/// but for specifying the value of the prime modulus Q.
#[macro_export]
macro_rules! zqu32_vec {
    ($($x:expr),* ; $Q:expr) => {{
        vec![ $($crate::zq::ZqU32::<$Q>::new($x)),* ]
    }};
}

/// A type representing an element of the ring Z/QZ.
///
/// ## Safety
/// Q should be an odd prime number. Although the primality of Q is not checked in the implementation,
/// its implementation makes this assumption for achieving some important properties of ring Z/QZ.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ZqU32<const Q: u32> {
    value: u32,
}

impl<const Q: u32> ZqU32<Q> {
    /// Creates a new `Zqu32` from the given value.
    pub fn new(value: u32) -> Self {
        Self {
            value: value.rem_euclid(Q),
        }
    }

    fn cast_new(value: u64) -> Self {
        Self {
            value: value.rem_euclid(Q as u64) as u32,
        }
    }
}

impl<const Q: u32> From<ZqU32<Q>> for u32 {
    fn from(value: ZqU32<Q>) -> Self {
        value.value
    }
}

impl<const Q: u32> From<u32> for ZqU32<Q> {
    fn from(value: u32) -> Self {
        Self::new(value)
    }
}

impl<const Q: u32> Zero for ZqU32<Q> {
    fn zero() -> Self {
        Self { value: 0 }
    }

    fn is_zero(&self) -> bool {
        self.value == 0
    }
}

impl<const Q: u32> One for ZqU32<Q> {
    fn one() -> Self {
        Self { value: 1 }
    }
}

impl<const Q: u32> Neg for ZqU32<Q> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        if self.value == 0 {
            Self { value: 0 }
        } else {
            Self {
                value: Q - self.value,
            }
        }
    }
}

impl<const Q: u32> Neg for &ZqU32<Q> {
    type Output = ZqU32<Q>;

    fn neg(self) -> Self::Output {
        if self.value == 0 {
            ZqU32 { value: 0 }
        } else {
            ZqU32 {
                value: Q - self.value,
            }
        }
    }
}

impl<const Q: u32> Add for ZqU32<Q> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        match self.value.checked_add(rhs.value) {
            Some(v) => Self::new(v),
            None => Self::cast_new(self.value as u64 + rhs.value as u64),
        }
    }
}

impl<const Q: u32> Add for &ZqU32<Q> {
    type Output = ZqU32<Q>;

    fn add(self, rhs: &ZqU32<Q>) -> Self::Output {
        match self.value.checked_add(rhs.value) {
            Some(v) => ZqU32::new(v),
            None => ZqU32::cast_new(self.value as u64 + rhs.value as u64),
        }
    }
}

impl<const Q: u32> Sub for ZqU32<Q> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        match self.value.checked_sub(rhs.value) {
            Some(v) => Self::new(v),
            None => Self::cast_new(Q as u64 + self.value as u64 - rhs.value as u64),
        }
    }
}

impl<const Q: u32> Sub for &ZqU32<Q> {
    type Output = ZqU32<Q>;

    fn sub(self, rhs: &ZqU32<Q>) -> Self::Output {
        match self.value.checked_sub(rhs.value) {
            Some(v) => ZqU32::new(v),
            None => ZqU32::cast_new(Q as u64 + self.value as u64 - rhs.value as u64),
        }
    }
}

impl<const Q: u32> Mul for ZqU32<Q> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        match self.value.checked_mul(rhs.value) {
            Some(v) => Self::new(v),
            None => Self::cast_new(self.value as u64 * rhs.value as u64),
        }
    }
}

impl<const Q: u32> Mul for &ZqU32<Q> {
    type Output = ZqU32<Q>;

    fn mul(self, rhs: &ZqU32<Q>) -> Self::Output {
        match self.value.checked_mul(rhs.value) {
            Some(v) => ZqU32::new(v),
            None => ZqU32::cast_new(self.value as u64 * rhs.value as u64),
        }
    }
}

impl<const Q: u32> Div for ZqU32<Q> {
    type Output = ZqU32<Q>;

    fn div(self, rhs: Self) -> Self::Output {
        use num::ToPrimitive;

        if rhs.is_zero() {
            panic!("division by zero");
        }
        let x = num::BigInt::from(rhs.value)
            .extended_gcd(&num::BigInt::from(Q))
            .x
            .mod_floor(&num::BigInt::from(Q))
            .to_u32()
            .unwrap();

        self.mul(ZqU32::new(x))
    }
}

impl<const Q: u32> Div for &ZqU32<Q> {
    type Output = ZqU32<Q>;

    fn div(self, rhs: &ZqU32<Q>) -> Self::Output {
        use num::ToPrimitive;
        if rhs.is_zero() {
            panic!("division by zero");
        }
        let x = num::BigInt::from(rhs.value)
            .extended_gcd(&num::BigInt::from(Q))
            .x
            .mod_floor(&num::BigInt::from(Q))
            .to_u32()
            .unwrap();

        self.mul(&ZqU32::new(x))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_zqu32_from() {
        const Q: u32 = 7;
        let a = ZqU32::<Q>::from(10);
        assert_eq!(a.value, 3);
    }

    #[test]
    fn test_zqu32_add() {
        const Q: u32 = 2147483647;

        let a = ZqU32::<Q>::new(Q - 1);
        let b = ZqU32::<Q>::one();
        let rp = &a + &b;
        let r = a.clone() + b.clone();
        assert_eq!(r, rp);
        assert!(r.value == 0);
    }

    #[test]
    fn test_zqu32_sub() {
        const Q: u32 = 2147483647;

        let a = ZqU32::<Q>::new(0);
        let b = ZqU32::<Q>::one();
        let rp = &a - &b;
        let r = a.clone() - b.clone();
        assert_eq!(r, rp);
        assert!(r.value == Q - 1);
    }

    #[test]
    fn test_zqu32_add_sub() {
        const Q: u32 = 7;

        // check all permutations of [0,1,2,3,4,5,6]
        for i in 0..=6 {
            for j in 0..=6 {
                let a = ZqU32::<Q>::new(i);
                let b = ZqU32::<Q>::new(j);
                let c = &a + &b;

                assert_eq!(&c - &a, b.clone());
                assert_eq!(&c - &b, a.clone());
            }
        }
    }

    #[test]
    fn test_zqu32_mul() {
        const Q: u32 = 7;

        let a = ZqU32::<Q>::new(4);
        let b = ZqU32::<Q>::new(5);
        let rp = &a * &b;
        let r = a.clone() * b.clone();
        assert_eq!(r, rp);
        // 4 * 5 = 20 = 6 mod 7
        assert!(r.value == 6);
    }

    #[test]
    fn test_zqu32_mul_overflow() {
        const Q: u32 = 2147483647;

        let a = ZqU32::<Q>::new(Q - 1);
        let b = ZqU32::<Q>::new(Q - 1);
        let rp = &a * &b;
        let r = a.clone() * b.clone();
        assert_eq!(r, rp);
        assert!(r.value <= Q - 1);
    }

    #[test]
    fn test_zqu32_div() {
        const Q: u32 = 7;

        // we had 4 * 5 = 20 = 6 mod 7, so 6 / 5 = 4 mod 7
        let a = ZqU32::<Q>::new(6);
        let b = ZqU32::<Q>::new(5);
        let rp = &a / &b;
        let r = a.clone() / b.clone();
        assert_eq!(r, rp);
        assert_eq!(r.value, 4);
    }

    #[test]
    fn test_zqu32_mui_div() {
        const Q: u32 = 7;

        // check all permutations of [0,1,2,3,4,5,6]
        for i in 0..=6 {
            for j in 0..=6 {
                let a = ZqU32::<Q>::new(i);
                let b = ZqU32::<Q>::new(j);
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
    fn test_zqu32_vec() {
        let v = zqu32_vec![12, 8, 0, 6; 7];
        let values = v.iter().map(|x| x.value).collect::<Vec<_>>();
        assert_eq!(values, vec![5, 1, 0, 6]);
    }
}
