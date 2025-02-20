use num::traits::{FromBytes, ToBytes};

use super::{ZqI32, ZqI64, ZqU32, ZqU64};

// Apply same implementation as num_traits::ops::bytes
macro_rules! impl_to_from_bytes {
    ($T:ty, $Z:tt, $L:ty) => {
        impl<const Q: $T> ToBytes for $Z<Q> {
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

        impl<const Q: $T> FromBytes for $Z<Q> {
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

impl_to_from_bytes!(i32, ZqI32, <i32 as ToBytes>::Bytes);
impl_to_from_bytes!(u32, ZqU32, <u32 as ToBytes>::Bytes);
impl_to_from_bytes!(i64, ZqI64, <i64 as ToBytes>::Bytes);
impl_to_from_bytes!(u64, ZqU64, <u64 as ToBytes>::Bytes);

#[cfg(test)]
mod test {
    use num::traits::{FromBytes, ToBytes};

    use super::*;

    #[test]
    fn test_bytes() {
        let zq = ZqI32::<7>::new(-3);
        assert_eq!(zq.to_be_bytes(), [255, 255, 255, 253]);
        assert_eq!(zq.to_le_bytes(), [253, 255, 255, 255]);

        let zq_be = ZqI32::<7>::from_be_bytes(&[255, 255, 255, 253]);
        let zq_le = ZqI32::<7>::from_le_bytes(&[253, 255, 255, 255]);
        assert_eq!(zq, zq_be);
        assert_eq!(zq, zq_le);

        let zq = ZqI64::<7>::new(-3);
        assert_eq!(zq.to_be_bytes(), [255, 255, 255, 255, 255, 255, 255, 253]);
        assert_eq!(zq.to_le_bytes(), [253, 255, 255, 255, 255, 255, 255, 255]);

        let zq_be = ZqI64::<7>::from_be_bytes(&[255, 255, 255, 255, 255, 255, 255, 253]);
        let zq_le = ZqI64::<7>::from_le_bytes(&[253, 255, 255, 255, 255, 255, 255, 255]);
        assert_eq!(zq, zq_be);
        assert_eq!(zq, zq_le);

        let zq = ZqU32::<7>::new(3);
        assert_eq!(zq.to_be_bytes(), [0, 0, 0, 3]);
        assert_eq!(zq.to_le_bytes(), [3, 0, 0, 0]);

        let zq_be = ZqU32::<7>::from_be_bytes(&[0, 0, 0, 3]);
        let zq_le = ZqU32::<7>::from_le_bytes(&[3, 0, 0, 0]);
        assert_eq!(zq, zq_be);
        assert_eq!(zq, zq_le);

        let zq = ZqU64::<7>::new(3);
        assert_eq!(zq.to_be_bytes(), [0, 0, 0, 0, 0, 0, 0, 3]);
        assert_eq!(zq.to_le_bytes(), [3, 0, 0, 0, 0, 0, 0, 0]);

        let zq_be = ZqU64::<7>::from_be_bytes(&[0, 0, 0, 0, 0, 0, 0, 3]);
        let zq_le = ZqU64::<7>::from_le_bytes(&[3, 0, 0, 0, 0, 0, 0, 0]);
        assert_eq!(zq, zq_be);
        assert_eq!(zq, zq_le);
    }
}
