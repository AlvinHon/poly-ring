use std::ops::{Add, Div, Mul, Neg, Sub};

use num::{BigInt, Integer, One, Zero};

use super::{ZqI128, ZqI32, ZqI64, ZqU32, ZqU64};

// ... Impl From ...

macro_rules! impl_from {
    ($T:ty, $Z:tt) => {
        impl<const Q: $T> From<$Z<Q>> for $T {
            fn from(value: $Z<Q>) -> Self {
                value.value
            }
        }

        impl<const Q: $T> From<$T> for $Z<Q> {
            fn from(value: $T) -> Self {
                Self::new(value)
            }
        }
    };
}

impl_from!(i32, ZqI32);
impl_from!(i64, ZqI64);
impl_from!(u32, ZqU32);
impl_from!(u64, ZqU64);
impl_from!(i128, ZqI128);

impl<const Q: i64> From<i32> for ZqI64<Q> {
    fn from(value: i32) -> Self {
        Self::new(value as i64)
    }
}

impl<const Q: i128> From<i32> for ZqI128<Q> {
    fn from(value: i32) -> Self {
        Self::new(value as i128)
    }
}

impl<const Q: i128> From<i64> for ZqI128<Q> {
    fn from(value: i64) -> Self {
        Self::new(value as i128)
    }
}

impl<const Q: u64> From<u32> for ZqU64<Q> {
    fn from(value: u32) -> Self {
        Self::new(value as u64)
    }
}

// ... Impl One ...
// ... Impl Zero ...

macro_rules! impl_one_zero_primitives {
    ($T:ty, $Z:tt) => {
        impl<const Q: $T> Zero for $Z<Q> {
            fn zero() -> Self {
                Self { value: 0 }
            }

            fn is_zero(&self) -> bool {
                self.value == 0
            }
        }

        impl<const Q: $T> One for $Z<Q> {
            fn one() -> Self {
                Self { value: 1 }
            }
        }
    };
}

impl_one_zero_primitives!(i32, ZqI32);
impl_one_zero_primitives!(i64, ZqI64);
impl_one_zero_primitives!(u32, ZqU32);
impl_one_zero_primitives!(u64, ZqU64);
impl_one_zero_primitives!(i128, ZqI128);

// ... Impl Neg ...

macro_rules! impl_neg_i {
    ($T:ty, $Z:tt) => {
        impl<const Q: $T> Neg for $Z<Q> {
            type Output = Self;

            fn neg(self) -> Self::Output {
                if self.value == 0 {
                    Self { value: 0 }
                } else {
                    Self { value: -self.value }
                }
            }
        }

        impl<const Q: $T> Neg for &$Z<Q> {
            type Output = $Z<Q>;

            fn neg(self) -> Self::Output {
                if self.value == 0 {
                    $Z { value: 0 }
                } else {
                    $Z { value: -self.value }
                }
            }
        }
    };
}

impl_neg_i!(i32, ZqI32);
impl_neg_i!(i64, ZqI64);
impl_neg_i!(i128, ZqI128);

macro_rules! impl_neg_u {
    ($T:ty, $Z:tt) => {
        impl<const Q: $T> Neg for $Z<Q> {
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

        impl<const Q: $T> Neg for &$Z<Q> {
            type Output = $Z<Q>;

            fn neg(self) -> Self::Output {
                if self.value == 0 {
                    $Z { value: 0 }
                } else {
                    $Z {
                        value: Q - self.value,
                    }
                }
            }
        }
    };
}

impl_neg_u!(u32, ZqU32);
impl_neg_u!(u64, ZqU64);

// ... Impl Add ...

macro_rules! impl_add {
    ($T:ty, $Z:tt) => {
        impl<const Q: $T> Add for $Z<Q> {
            type Output = Self;

            fn add(self, rhs: Self) -> Self::Output {
                match self.value.checked_add(rhs.value) {
                    Some(v) => Self::new(v),
                    None => Self::safe_new(BigInt::from(self.value) + BigInt::from(rhs.value)),
                }
            }
        }

        impl<const Q: $T> Add for &$Z<Q> {
            type Output = $Z<Q>;

            fn add(self, rhs: Self) -> Self::Output {
                match self.value.checked_add(rhs.value) {
                    Some(v) => $Z::new(v),
                    None => $Z::safe_new(BigInt::from(self.value) + BigInt::from(rhs.value)),
                }
            }
        }
    };
}

impl_add!(i32, ZqI32);
impl_add!(i64, ZqI64);
impl_add!(i128, ZqI128);
impl_add!(u32, ZqU32);
impl_add!(u64, ZqU64);

// ... Impl Sub ...

macro_rules! impl_sub_i {
    ($T:ty, $Z:tt) => {
        impl<const Q: $T> Sub for $Z<Q> {
            type Output = Self;

            fn sub(self, rhs: Self) -> Self::Output {
                match self.value.checked_sub(rhs.value) {
                    Some(v) => Self::new(v),
                    None => Self::safe_new(BigInt::from(self.value) - BigInt::from(rhs.value)),
                }
            }
        }

        impl<const Q: $T> Sub for &$Z<Q> {
            type Output = $Z<Q>;

            fn sub(self, rhs: Self) -> Self::Output {
                match self.value.checked_sub(rhs.value) {
                    Some(v) => $Z::new(v),
                    None => $Z::safe_new(BigInt::from(self.value) - BigInt::from(rhs.value)),
                }
            }
        }
    };
}

impl_sub_i!(i32, ZqI32);
impl_sub_i!(i64, ZqI64);
impl_sub_i!(i128, ZqI128);

macro_rules! impl_sub_u {
    ($T:ty, $Z:tt) => {
        impl<const Q: $T> Sub for $Z<Q> {
            type Output = Self;

            fn sub(self, rhs: Self) -> Self::Output {
                match self.value.checked_sub(rhs.value) {
                    Some(v) => Self::new(v),
                    None => Self::safe_new(
                        BigInt::from(Q) + BigInt::from(self.value) - BigInt::from(rhs.value),
                    ),
                }
            }
        }

        impl<const Q: $T> Sub for &$Z<Q> {
            type Output = $Z<Q>;

            fn sub(self, rhs: Self) -> Self::Output {
                match self.value.checked_sub(rhs.value) {
                    Some(v) => $Z::new(v),
                    None => $Z::safe_new(
                        BigInt::from(Q) + BigInt::from(self.value) - BigInt::from(rhs.value),
                    ),
                }
            }
        }
    };
}

impl_sub_u!(u32, ZqU32);
impl_sub_u!(u64, ZqU64);

// ... Impl Mul ...

macro_rules! impl_mul {
    ($T:ty, $Z:tt) => {
        impl<const Q: $T> Mul for $Z<Q> {
            type Output = Self;

            fn mul(self, rhs: Self) -> Self::Output {
                match self.value.checked_mul(rhs.value) {
                    Some(v) => Self::new(v),
                    None => Self::safe_new(BigInt::from(self.value) * BigInt::from(rhs.value)),
                }
            }
        }

        impl<const Q: $T> Mul for &$Z<Q> {
            type Output = $Z<Q>;

            fn mul(self, rhs: Self) -> Self::Output {
                match self.value.checked_mul(rhs.value) {
                    Some(v) => $Z::new(v),
                    None => $Z::safe_new(BigInt::from(self.value) * BigInt::from(rhs.value)),
                }
            }
        }
    };
}

impl_mul!(i32, ZqI32);
impl_mul!(i64, ZqI64);
impl_mul!(i128, ZqI128);
impl_mul!(u32, ZqU32);
impl_mul!(u64, ZqU64);

// ... Impl Div ...

macro_rules! impl_div_i {
    ($T:ty, $Z:tt) => {
        impl<const Q: $T> Div for $Z<Q> {
            type Output = $Z<Q>;

            fn div(self, rhs: Self) -> Self::Output {
                if rhs.is_zero() {
                    panic!("division by zero");
                }
                let x = rhs.value.extended_gcd(&Q).x;
                self.mul($Z::new(x))
            }
        }

        impl<const Q: $T> Div for &$Z<Q> {
            type Output = $Z<Q>;

            fn div(self, rhs: Self) -> Self::Output {
                if rhs.is_zero() {
                    panic!("division by zero");
                }
                let x = rhs.value.extended_gcd(&Q).x;
                self.mul(&$Z::new(x))
            }
        }
    };
}

impl_div_i!(i32, ZqI32);
impl_div_i!(i64, ZqI64);
impl_div_i!(i128, ZqI128);

macro_rules! impl_div_u {
    ($T:ty, $Z:tt) => {
        impl<const Q: $T> Div for $Z<Q> {
            type Output = $Z<Q>;

            fn div(self, rhs: Self) -> Self::Output {
                if rhs.is_zero() {
                    panic!("division by zero");
                }
                let x = num::BigInt::from(rhs.value)
                    .extended_gcd(&num::BigInt::from(Q))
                    .x
                    .mod_floor(&num::BigInt::from(Q))
                    .try_into()
                    .unwrap();
                self.mul($Z::new(x))
            }
        }

        impl<const Q: $T> Div for &$Z<Q> {
            type Output = $Z<Q>;

            fn div(self, rhs: Self) -> Self::Output {
                if rhs.is_zero() {
                    panic!("division by zero");
                }
                let x = num::BigInt::from(rhs.value)
                    .extended_gcd(&num::BigInt::from(Q))
                    .x
                    .mod_floor(&num::BigInt::from(Q))
                    .try_into()
                    .unwrap();

                self.mul(&$Z::new(x))
            }
        }
    };
}

impl_div_u!(u32, ZqU32);
impl_div_u!(u64, ZqU64);

#[cfg(test)]
mod zqi32_tests {
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
        assert!(r.value <= Q / 2 && r.value >= -Q / 2);

        let a = ZqI32::<Q>::new(Q / 2);
        let b = ZqI32::<Q>::new(-Q / 2);
        let rp = &a * &b;
        let r2 = a.clone() * b.clone();
        assert_eq!(r2, rp);
        assert!(r2.value <= Q / 2 && r2.value >= -Q / 2);
        assert!(r.value == -r2.value);
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
}

#[cfg(test)]
mod zqi64_tests {
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
        assert!(r.value <= Q / 2 && r.value >= -Q / 2);

        let a = ZqI64::<Q>::new(Q / 2);
        let b = ZqI64::<Q>::new(-Q / 2);
        let rp = &a * &b;
        let r2 = a.clone() * b.clone();
        assert_eq!(r2, rp);
        assert!(r2.value <= Q / 2 && r2.value >= -Q / 2);
        assert!(r.value == -r2.value);
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
}

#[cfg(test)]
mod zqi128_tests {
    use super::*;

    #[test]
    fn test_zqi128_from() {
        const Q: i128 = 7;

        let a = ZqI128::<Q>::from(10i128);
        assert_eq!(a.value, 3);

        let b = ZqI128::<Q>::from(-10i128);
        assert_eq!(b.value, -3);
    }

    #[test]
    fn test_zqi128_add() {
        const Q: i128 = 604462909807314587353021;

        let a = ZqI128::<Q>::new(Q / 2);
        let b = ZqI128::<Q>::one();
        let rp = &a + &b;
        let r = a.clone() + b.clone();
        assert_eq!(r, rp);
        assert!(r.value == -Q / 2);
    }

    #[test]
    fn test_zqi128_sub() {
        const Q: i128 = 604462909807314587353021;

        let a = ZqI128::<Q>::new(-Q / 2);
        let b = ZqI128::<Q>::one();
        let rp = &a - &b;
        let r = a.clone() - b.clone();
        assert_eq!(r, rp);
        assert!(r.value == Q / 2);
    }

    #[test]
    fn test_zqi128_add_sub() {
        const Q: i128 = 7;

        // check all permutations of [-3,-2,-1,0,1,2,3]
        for i in -3..=3 {
            for j in -3..=3 {
                let a = ZqI128::<Q>::new(i);
                let b = ZqI128::<Q>::new(j);
                let c = &a + &b;

                assert_eq!(&c - &a, b.clone());
                assert_eq!(&c - &b, a.clone());
            }
        }
    }

    #[test]
    fn test_zqi128_mul() {
        const Q: i128 = 7;

        // [-3,-2,-1,0,1,2,3] <-> [4,5,6,0,1,2,3]
        let a = ZqI128::<Q>::new(-3);
        let b = ZqI128::<Q>::new(-2);
        let rp = &a * &b;
        let r = a.clone() * b.clone();
        assert_eq!(r, rp);
        // -3 * -2 = 6 = -1 mod 7
        assert!(r.value == -1);
    }

    #[test]
    fn test_zqi128_mul_overflow() {
        const Q: i128 = 604462909807314587353021;

        let a = ZqI128::<Q>::new(Q / 2);
        let b = ZqI128::<Q>::new(Q / 2);
        let rp = &a * &b;
        let r = a.clone() * b.clone();
        assert_eq!(r, rp);
        assert!(r.value <= Q / 2 && r.value >= -Q / 2);

        let a = ZqI128::<Q>::new(Q / 2);
        let b = ZqI128::<Q>::new(-Q / 2);
        let rp = &a * &b;
        let r2 = a.clone() * b.clone();
        assert_eq!(r2, rp);
        assert!(r2.value <= Q / 2 && r2.value >= -Q / 2);
        assert!(r.value == -r2.value);
    }

    #[test]
    fn test_zqi128_div() {
        const Q: i128 = 7;

        // [-3,-2,-1,0,1,2,3] <-> [4,5,6,0,1,2,3]
        // we had -3 * -2 = 6 = -1 mod 7, so -1 / -2 = -3 mod 7
        let a = ZqI128::<Q>::new(-1);
        let b = ZqI128::<Q>::new(-2);
        let rp = &a / &b;
        let r = a.clone() / b.clone();
        assert_eq!(r, rp);
        assert_eq!(r.value, -3);
    }

    #[test]
    #[should_panic]
    fn test_zqi128_div_zero() {
        const Q: i128 = 7;

        let a = ZqI128::<Q>::one();
        let b = ZqI128::<Q>::zero();
        let _ = &a / &b;
    }

    #[test]
    fn test_zqi128_mui_div() {
        const Q: i128 = 7;

        // check all permutations of [-3,-2,-1,0,1,2,3]
        for i in -3..=3 {
            for j in -3..=3 {
                let a = ZqI128::<Q>::new(i);
                let b = ZqI128::<Q>::new(j);
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
}

#[cfg(test)]
mod zqu32_tests {
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
    #[should_panic]
    fn test_zqu32_div_zero() {
        const Q: u32 = 7;

        let a = ZqU32::<Q>::one();
        let b = ZqU32::<Q>::zero();
        let _ = &a / &b;
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
}

#[cfg(test)]
mod zqu64_tests {
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
    fn test_zqu64_add_sub() {
        const Q: u64 = 7;

        // check all permutations of [0,1,2,3,4,5,6]
        for i in 0..=6 {
            for j in 0..=6 {
                let a = ZqU64::<Q>::new(i);
                let b = ZqU64::<Q>::new(j);
                let c = &a + &b;

                assert_eq!(&c - &a, b.clone());
                assert_eq!(&c - &b, a.clone());
            }
        }
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
    fn test_zqu64_div() {
        const Q: u64 = 7;

        // we had 4 * 5 = 20 = 6 mod 7, so 6 / 5 = 4 mod 7
        let a = ZqU64::<Q>::new(6);
        let b = ZqU64::<Q>::new(5);
        let rp = &a / &b;
        let r = a.clone() / b.clone();
        assert_eq!(r, rp);
        assert_eq!(r.value, 4);
    }

    #[test]
    #[should_panic]
    fn test_zqu64_div_zero() {
        const Q: u64 = 7;

        let a = ZqU64::<Q>::one();
        let b = ZqU64::<Q>::zero();
        let _ = &a / &b;
    }

    #[test]
    fn test_zqu64_mui_div() {
        const Q: u64 = 7;

        // check all permutations of [0,1,2,3,4,5,6]
        for i in 0..=6 {
            for j in 0..=6 {
                let a = ZqU64::<Q>::new(i);
                let b = ZqU64::<Q>::new(j);
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
}
