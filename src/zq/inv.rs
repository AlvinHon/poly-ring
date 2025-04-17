use num::{traits::Inv, Integer, Zero};

use super::{ZqI128, ZqI32, ZqI64, ZqU128, ZqU32, ZqU64};

macro_rules! impl_inv_zqi {
    ($T:ty, $Z:tt) => {
        impl<const Q: $T> Inv for $Z<Q> {
            type Output = Self;

            fn inv(self) -> Self::Output {
                if self.is_zero() {
                    panic!("division by zero");
                }
                let x = self.value.extended_gcd(&Q).x;
                Self::new(x)
            }
        }

        impl<const Q: $T> Inv for &$Z<Q> {
            type Output = $Z<Q>;

            fn inv(self) -> Self::Output {
                if self.is_zero() {
                    panic!("division by zero");
                }
                let x = self.value.extended_gcd(&Q).x;
                $Z::new(x)
            }
        }
    };
}

impl_inv_zqi!(i32, ZqI32);
impl_inv_zqi!(i64, ZqI64);
impl_inv_zqi!(i128, ZqI128);

macro_rules! impl_inv_zqu {
    ($T:ty, $Z:tt) => {
        impl<const Q: $T> Inv for $Z<Q> {
            type Output = Self;

            fn inv(self) -> Self::Output {
                if self.is_zero() {
                    panic!("division by zero");
                }
                let x = num::BigInt::from(self.value)
                    .extended_gcd(&num::BigInt::from(Q))
                    .x
                    .mod_floor(&num::BigInt::from(Q))
                    .try_into()
                    .unwrap();
                $Z::new(x)
            }
        }

        impl<const Q: $T> Inv for &$Z<Q> {
            type Output = $Z<Q>;

            fn inv(self) -> Self::Output {
                if self.is_zero() {
                    panic!("division by zero");
                }
                let x = num::BigInt::from(self.value)
                    .extended_gcd(&num::BigInt::from(Q))
                    .x
                    .mod_floor(&num::BigInt::from(Q))
                    .try_into()
                    .unwrap();
                $Z::new(x)
            }
        }
    };
}

impl_inv_zqu!(u32, ZqU32);
impl_inv_zqu!(u64, ZqU64);
impl_inv_zqu!(u128, ZqU128);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_zqi32_inv() {
        const Q: i32 = 7;

        // [-3,-2,-1,0,1,2,3] <-> [4,5,6,0,1,2,3]
        // 2 * -3 = -6 = 1 mod 7, so 2^-1 = -3 mod 7
        let a = ZqI32::<Q>::new(2);
        let rp = (&a).inv();
        let r = a.clone().inv();
        assert_eq!(r, rp);
        assert_eq!(r.value, -3);
    }

    #[test]
    #[should_panic]
    fn test_zqi32_inv_by_zero() {
        ZqI32::<7>::new(0).inv();
    }

    #[test]
    #[should_panic]
    fn test_zqi32_clone_inv_by_zero() {
        ZqI32::<7>::new(0).clone().inv();
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
    #[should_panic]
    fn test_zqi64_inv_by_zero() {
        ZqI64::<7>::new(0).inv();
    }

    #[test]
    #[should_panic]
    fn test_zqi64_inv_clone_by_zero() {
        ZqI64::<7>::new(0).clone().inv();
    }

    #[test]
    fn test_zqi128_inv() {
        const Q: i128 = 7;

        // [-3,-2,-1,0,1,2,3] <-> [4,5,6,0,1,2,3]
        // 2 * -3 = -6 = 1 mod 7, so 2^-1 = -3 mod 7
        let a = ZqI128::<Q>::new(2);
        let rp = (&a).inv();
        let r = a.clone().inv();
        assert_eq!(r, rp);
        assert_eq!(r.value, -3);
    }

    #[test]
    #[should_panic]
    fn test_zqi128_inv_by_zero() {
        ZqI128::<7>::new(0).inv();
    }

    #[test]
    #[should_panic]
    fn test_zqi128_inv_clone_by_zero() {
        ZqI128::<7>::new(0).clone().inv();
    }

    #[test]
    fn test_zqu32_inv() {
        const Q: u32 = 7;

        // 2 * 4 = 8 = 1 mod 7, so 2^-1 = 4 mod 7
        let a = ZqU32::<Q>::new(2);
        let rp = (&a).inv();
        let r = a.clone().inv();
        assert_eq!(r, rp);
        assert_eq!(r.value, 4);
    }

    #[test]
    #[should_panic]
    fn test_zqu32_inv_by_zero() {
        ZqU32::<7>::new(0).inv();
    }

    #[test]
    #[should_panic]
    fn test_zqu32_inv_clone_by_zero() {
        ZqU32::<7>::new(0).clone().inv();
    }

    #[test]
    fn test_zqu64_inv() {
        const Q: u64 = 7;

        // 2 * 4 = 8 = 1 mod 7, so 2^-1 = 4 mod 7
        let a = ZqU64::<Q>::new(2);
        let rp = (&a).inv();
        let r = a.clone().inv();
        assert_eq!(r, rp);
        assert_eq!(r.value, 4);
    }

    #[test]
    #[should_panic]
    fn test_zqu64_inv_by_zero() {
        ZqU64::<7>::new(0).inv();
    }

    #[test]
    #[should_panic]
    fn test_zqu64_inv_clone_by_zero() {
        ZqU64::<7>::new(0).clone().inv();
    }

    #[test]
    fn test_zqu128_inv() {
        const Q: u128 = 7;

        // 2 * 4 = 8 = 1 mod 7, so 2^-1 = 4 mod 7
        let a = ZqU128::<Q>::new(2);
        let rp = (&a).inv();
        let r = a.clone().inv();
        assert_eq!(r, rp);
        assert_eq!(r.value, 4);
    }

    #[test]
    #[should_panic]
    fn test_zqu128_inv_by_zero() {
        ZqU128::<7>::new(0).inv();
    }

    #[test]
    #[should_panic]
    fn test_zqu128_inv_clone_by_zero() {
        ZqU128::<7>::new(0).clone().inv();
    }
}
