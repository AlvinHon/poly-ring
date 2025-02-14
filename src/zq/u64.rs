use std::ops::{Add, Mul, Neg, Sub};

use num::{One, Zero};

/// A macro to create a vector of `ZqU64`. It transforms the following code:
///
/// ```ignore
/// zqu64_vec![1,2,3 ; Q]
/// ```
///
/// into
///
/// ```ignore
/// vec![ZqU64::<Q>::new(1), ZqU64::<Q>::new(2), ZqU64::<Q>::new(3)]
/// ```
///
/// Please note the semi-colon `;` is not for specifying the length of the vector (as vec! macro does),
/// but for specifying the value of the prime modulus Q.
#[macro_export]
macro_rules! zqu64_vec {
    ($($x:expr),* ; $Q:expr) => {{
        vec![ $($crate::zq::ZqU64::<$Q>::new($x)),* ]
    }};
}

/// A type representing an element of the ring Z/QZ.
///
/// ## Safety
/// Q should be an odd prime number. Although the primality of Q is not checked in the implementation,
/// its implementation makes this assumption for achieving some important properties of ring Z/QZ.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ZqU64<const Q: u64> {
    value: u64,
}

impl<const Q: u64> ZqU64<Q> {
    /// Creates a new `Zqu64` from the given value. It normalizes the value to the range \[-Q/2, Q/2\).
    pub fn new(value: u64) -> Self {
        Self {
            value: value.rem_euclid(Q),
        }
    }

    fn cast_new(value: u128) -> Self {
        Self {
            value: value.rem_euclid(Q as u128) as u64,
        }
    }
}

impl<const Q: u64> From<ZqU64<Q>> for u64 {
    fn from(value: ZqU64<Q>) -> Self {
        value.value
    }
}

impl<const Q: u64> From<u32> for ZqU64<Q> {
    fn from(value: u32) -> Self {
        Self::new(value as u64)
    }
}

impl<const Q: u64> From<u64> for ZqU64<Q> {
    fn from(value: u64) -> Self {
        Self::new(value)
    }
}

impl<const Q: u64> Zero for ZqU64<Q> {
    fn zero() -> Self {
        Self { value: 0 }
    }

    fn is_zero(&self) -> bool {
        self.value == 0
    }
}

impl<const Q: u64> One for ZqU64<Q> {
    fn one() -> Self {
        Self { value: 1 }
    }
}

impl<const Q: u64> Neg for ZqU64<Q> {
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

impl<const Q: u64> Neg for &ZqU64<Q> {
    type Output = ZqU64<Q>;

    fn neg(self) -> Self::Output {
        if self.value == 0 {
            ZqU64 { value: 0 }
        } else {
            ZqU64 {
                value: Q - self.value,
            }
        }
    }
}

impl<const Q: u64> Add for ZqU64<Q> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        match self.value.checked_add(rhs.value) {
            Some(v) => Self::new(v),
            None => Self::cast_new(self.value as u128 + rhs.value as u128),
        }
    }
}

impl<const Q: u64> Add for &ZqU64<Q> {
    type Output = ZqU64<Q>;

    fn add(self, rhs: &ZqU64<Q>) -> Self::Output {
        match self.value.checked_add(rhs.value) {
            Some(v) => ZqU64::new(v),
            None => ZqU64::cast_new(self.value as u128 + rhs.value as u128),
        }
    }
}

impl<const Q: u64> Sub for ZqU64<Q> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        match self.value.checked_sub(rhs.value) {
            Some(v) => Self::new(v),
            None => Self::cast_new(Q as u128 + self.value as u128 - rhs.value as u128),
        }
    }
}

impl<const Q: u64> Sub for &ZqU64<Q> {
    type Output = ZqU64<Q>;

    fn sub(self, rhs: &ZqU64<Q>) -> Self::Output {
        match self.value.checked_sub(rhs.value) {
            Some(v) => ZqU64::new(v),
            None => ZqU64::cast_new(Q as u128 + self.value as u128 - rhs.value as u128),
        }
    }
}

impl<const Q: u64> Mul for ZqU64<Q> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        match self.value.checked_mul(rhs.value) {
            Some(v) => Self::new(v),
            None => Self::cast_new(self.value as u128 * rhs.value as u128),
        }
    }
}

impl<const Q: u64> Mul for &ZqU64<Q> {
    type Output = ZqU64<Q>;

    fn mul(self, rhs: &ZqU64<Q>) -> Self::Output {
        match self.value.checked_mul(rhs.value) {
            Some(v) => ZqU64::new(v),
            None => ZqU64::cast_new(self.value as u128 * rhs.value as u128),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_zqu64_from() {
        const Q: u64 = 7;
        let a = ZqU64::<Q>::from(10u64);
        assert_eq!(a.value, 3);
    }

    #[test]
    fn test_zqu64_add() {
        const Q: u64 = 416608695821;

        let a = ZqU64::<Q>::new(Q - 1);
        let b = ZqU64::<Q>::one();
        let rp = &a + &b;
        let r = a.clone() + b.clone();
        assert_eq!(r, rp);
        assert!(r.value == 0);
    }

    #[test]
    fn test_zqu64_sub() {
        const Q: u64 = 416608695821;

        let a = ZqU64::<Q>::new(0);
        let b = ZqU64::<Q>::one();
        let rp = &a - &b;
        let r = a.clone() - b.clone();
        assert_eq!(r, rp);
        assert!(r.value == Q - 1);
    }

    #[test]
    fn test_zqu64_mul() {
        const Q: u64 = 7;

        let a = ZqU64::<Q>::new(4);
        let b = ZqU64::<Q>::new(5);
        let rp = &a * &b;
        let r = a.clone() * b.clone();
        assert_eq!(r, rp);
        // 4 * 5 = 20 = 6 mod 7
        assert!(r.value == 6);
    }

    #[test]
    fn test_zqu64_mul_overflow() {
        const Q: u64 = 416608695821;

        let a = ZqU64::<Q>::new(Q - 1);
        let b = ZqU64::<Q>::new(Q - 1);
        let rp = &a * &b;
        let r = a.clone() * b.clone();
        assert_eq!(r, rp);
        assert!(r.value <= Q - 1);
    }

    #[test]
    fn test_zqu64_vec() {
        let v = zqu64_vec![12, 8, 0, 6; 7];
        let values = v.iter().map(|x| x.value).collect::<Vec<_>>();
        assert_eq!(values, vec![5, 1, 0, 6]);
    }
}
