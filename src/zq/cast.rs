use num::{FromPrimitive, ToPrimitive};

use super::{ZqI128, ZqI32, ZqI64, ZqU128, ZqU32, ZqU64};

macro_rules! impl_to_primitive {
    ($T:ty, $Z:tt) => {
        impl<const Q: $T> ToPrimitive for $Z<Q> {
            fn to_i64(&self) -> Option<i64> {
                <$T as ToPrimitive>::to_i64(&self.value)
            }

            fn to_u64(&self) -> Option<u64> {
                <$T as ToPrimitive>::to_u64(&self.value)
            }
        }
    };
}

macro_rules! impl_to_primitive_more {
    ($T:ty, $Z:tt) => {
        impl<const Q: $T> ToPrimitive for $Z<Q> {
            fn to_i64(&self) -> Option<i64> {
                <$T as ToPrimitive>::to_i64(&self.value)
            }

            fn to_u64(&self) -> Option<u64> {
                <$T as ToPrimitive>::to_u64(&self.value)
            }

            fn to_i128(&self) -> Option<i128> {
                <$T as ToPrimitive>::to_i128(&self.value)
            }

            fn to_u128(&self) -> Option<u128> {
                <$T as ToPrimitive>::to_u128(&self.value)
            }
        }
    };
}

impl_to_primitive!(i32, ZqI32);
impl_to_primitive!(i64, ZqI64);
impl_to_primitive_more!(i128, ZqI128);
impl_to_primitive!(u32, ZqU32);
impl_to_primitive!(u64, ZqU64);
impl_to_primitive_more!(u128, ZqU128);

macro_rules! impl_from_primitive {
    ($T:ty, $Z:tt) => {
        impl<const Q: $T> FromPrimitive for $Z<Q> {
            fn from_i64(n: i64) -> Option<Self> {
                <$T as FromPrimitive>::from_i64(n).map(Self::new)
            }

            fn from_u64(n: u64) -> Option<Self> {
                <$T as FromPrimitive>::from_u64(n).map(Self::new)
            }
        }
    };
}

macro_rules! impl_from_primitive_more {
    ($T:ty, $Z:tt) => {
        impl<const Q: $T> FromPrimitive for $Z<Q> {
            fn from_i64(n: i64) -> Option<Self> {
                <$T as FromPrimitive>::from_i64(n).map(Self::new)
            }

            fn from_u64(n: u64) -> Option<Self> {
                <$T as FromPrimitive>::from_u64(n).map(Self::new)
            }

            fn from_i128(n: i128) -> Option<Self> {
                <$T as FromPrimitive>::from_i128(n).map(Self::new)
            }

            fn from_u128(n: u128) -> Option<Self> {
                <$T as FromPrimitive>::from_u128(n).map(Self::new)
            }
        }
    };
}

impl_from_primitive!(i32, ZqI32);
impl_from_primitive!(i64, ZqI64);
impl_from_primitive_more!(i128, ZqI128);
impl_from_primitive!(u32, ZqU32);
impl_from_primitive!(u64, ZqU64);
impl_from_primitive_more!(u128, ZqU128);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_i32_from_to_primitive() {
        let zq = ZqI32::<7>::new(3);
        assert_eq!(zq.to_i64(), Some(3));
        assert_eq!(zq.to_u64(), Some(3));

        let zq = ZqI32::<7>::new(-3);
        assert_eq!(zq.to_i64(), Some(-3));
        assert_eq!(zq.to_u64(), None);

        assert_eq!(ZqI32::<7>::from_i64(3), Some(ZqI32::<7>::new(3)));
        assert_eq!(ZqI32::<7>::from_i64(10), Some(ZqI32::<7>::new(3)));
        assert_eq!(ZqI32::<7>::from_i64(-3), Some(ZqI32::<7>::new(-3)));
        assert_eq!(ZqI32::<7>::from_i64(-10), Some(ZqI32::<7>::new(-3)));

        assert_eq!(ZqI32::<7>::from_u64(3), Some(ZqI32::<7>::new(3)));
        assert_eq!(ZqI32::<7>::from_u64(10), Some(ZqI32::<7>::new(3)));
    }

    #[test]
    fn test_u32_from_to_primitive() {
        let zq = ZqU32::<7>::new(3);
        assert_eq!(zq.to_i64(), Some(3));
        assert_eq!(zq.to_u64(), Some(3));

        let zq = ZqU32::<7>::new(10);
        assert_eq!(zq.to_i64(), Some(3));
        assert_eq!(zq.to_u64(), Some(3));

        assert_eq!(ZqU32::<7>::from_i64(3), Some(ZqU32::<7>::new(3)));
        assert_eq!(ZqU32::<7>::from_i64(10), Some(ZqU32::<7>::new(3)));
        assert_eq!(ZqU32::<7>::from_i64(-3), None);
        assert_eq!(ZqU32::<7>::from_i64(-10), None);

        assert_eq!(ZqU32::<7>::from_u64(3), Some(ZqU32::<7>::new(3)));
        assert_eq!(ZqU32::<7>::from_u64(10), Some(ZqU32::<7>::new(3)));
    }

    #[test]
    fn test_i64_from_to_primitive() {
        let zq = ZqI64::<7>::new(3);
        assert_eq!(zq.to_i64(), Some(3));
        assert_eq!(zq.to_u64(), Some(3));

        let zq = ZqI64::<7>::new(-3);
        assert_eq!(zq.to_i64(), Some(-3));
        assert_eq!(zq.to_u64(), None);

        assert_eq!(ZqI64::<7>::from_i64(3), Some(ZqI64::<7>::new(3)));
        assert_eq!(ZqI64::<7>::from_i64(10), Some(ZqI64::<7>::new(3)));
        assert_eq!(ZqI64::<7>::from_i64(-3), Some(ZqI64::<7>::new(-3)));
        assert_eq!(ZqI64::<7>::from_i64(-10), Some(ZqI64::<7>::new(-3)));

        assert_eq!(ZqI64::<7>::from_u64(3), Some(ZqI64::<7>::new(3)));
        assert_eq!(ZqI64::<7>::from_u64(10), Some(ZqI64::<7>::new(3)));
    }

    #[test]
    fn test_u64_from_to_primitive() {
        let zq = ZqU64::<7>::new(3);
        assert_eq!(zq.to_i64(), Some(3));
        assert_eq!(zq.to_u64(), Some(3));

        let zq = ZqU64::<7>::new(10);
        assert_eq!(zq.to_i64(), Some(3));
        assert_eq!(zq.to_u64(), Some(3));

        assert_eq!(ZqU64::<7>::from_i64(3), Some(ZqU64::<7>::new(3)));
        assert_eq!(ZqU64::<7>::from_i64(10), Some(ZqU64::<7>::new(3)));
        assert_eq!(ZqU64::<7>::from_i64(-3), None);
        assert_eq!(ZqU64::<7>::from_i64(-10), None);

        assert_eq!(ZqU64::<7>::from_u64(3), Some(ZqU64::<7>::new(3)));
        assert_eq!(ZqU64::<7>::from_u64(10), Some(ZqU64::<7>::new(3)));
    }

    #[test]
    fn test_i128_from_to_primitive() {
        let zq = ZqI128::<7>::new(3);
        assert_eq!(zq.to_i64(), Some(3));
        assert_eq!(zq.to_u64(), Some(3));
        assert_eq!(zq.to_i128(), Some(3));
        assert_eq!(zq.to_u128(), Some(3));

        let zq = ZqI128::<7>::new(-3);
        assert_eq!(zq.to_i64(), Some(-3));
        assert_eq!(zq.to_u64(), None);
        assert_eq!(zq.to_i128(), Some(-3));
        assert_eq!(zq.to_u128(), None);

        assert_eq!(ZqI128::<7>::from_i64(3), Some(ZqI128::<7>::new(3)));
        assert_eq!(ZqI128::<7>::from_i64(10), Some(ZqI128::<7>::new(3)));
        assert_eq!(ZqI128::<7>::from_i64(-3), Some(ZqI128::<7>::new(-3)));
        assert_eq!(ZqI128::<7>::from_i64(-10), Some(ZqI128::<7>::new(-3)));

        assert_eq!(ZqI128::<7>::from_u64(3), Some(ZqI128::<7>::new(3)));
        assert_eq!(ZqI128::<7>::from_u64(10), Some(ZqI128::<7>::new(3)));
    }

    #[test]
    fn test_u128_from_to_primitive() {
        let zq = ZqU128::<7>::new(3);
        assert_eq!(zq.to_i64(), Some(3));
        assert_eq!(zq.to_u64(), Some(3));
        assert_eq!(zq.to_i128(), Some(3));
        assert_eq!(zq.to_u128(), Some(3));

        let zq = ZqU128::<7>::new(10);
        assert_eq!(zq.to_i64(), Some(3));
        assert_eq!(zq.to_u64(), Some(3));
        assert_eq!(zq.to_i128(), Some(3));
        assert_eq!(zq.to_u128(), Some(3));

        assert_eq!(ZqU128::<7>::from_i64(3), Some(ZqU128::<7>::new(3)));
        assert_eq!(ZqU128::<7>::from_i64(10), Some(ZqU128::<7>::new(3)));
        assert_eq!(ZqU128::<7>::from_i64(-3), None);
        assert_eq!(ZqU128::<7>::from_i64(-10), None);

        assert_eq!(ZqU128::<7>::from_u64(3), Some(ZqU128::<7>::new(3)));
        assert_eq!(ZqU128::<7>::from_u64(10), Some(ZqU128::<7>::new(3)));
    }
}
