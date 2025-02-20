use num::traits::{FromBytes, ToBytes};

use super::{ZqI32, ZqI64, ZqU32, ZqU64};

// Apply same implementation as num_traits::ops::bytes
macro_rules! impl_to_from_bytes {
    ($T:ty, $Z:ty, $L:ty) => {
        impl<const Q: $T> ToBytes for $Z {
            type Bytes = $L;

            #[inline]
            fn to_be_bytes(&self) -> Self::Bytes {
                <$T as ToBytes>::to_be_bytes(&self.value)
            }

            #[inline]
            fn to_le_bytes(&self) -> Self::Bytes {
                <$T as ToBytes>::to_le_bytes(&self.value)
            }

            #[inline]
            fn to_ne_bytes(&self) -> Self::Bytes {
                <$T as ToBytes>::to_ne_bytes(&self.value)
            }
        }

        impl<const Q: $T> FromBytes for $Z {
            type Bytes = $L;

            #[inline]
            fn from_be_bytes(bytes: &Self::Bytes) -> Self {
                <$T as FromBytes>::from_be_bytes(bytes).into()
            }

            #[inline]
            fn from_le_bytes(bytes: &Self::Bytes) -> Self {
                <$T as FromBytes>::from_le_bytes(bytes).into()
            }

            #[inline]
            fn from_ne_bytes(bytes: &Self::Bytes) -> Self {
                <$T as FromBytes>::from_ne_bytes(bytes).into()
            }
        }
    };
}

impl_to_from_bytes!(i32, ZqI32<Q>, <i32 as ToBytes>::Bytes);
impl_to_from_bytes!(u32, ZqU32<Q>, <u32 as ToBytes>::Bytes);
impl_to_from_bytes!(i64, ZqI64<Q>, <i64 as ToBytes>::Bytes);
impl_to_from_bytes!(u64, ZqU64<Q>, <u64 as ToBytes>::Bytes);
