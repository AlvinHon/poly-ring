use num::{
    traits::{ConstOne, ConstZero},
    One, Zero,
};

use crate::zq::{ZqI128, ZqI32, ZqI64, ZqU128, ZqU32, ZqU64};

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

        impl<const Q: $T> ConstZero for $Z<Q> {
            const ZERO: Self = Self { value: 0 };
        }

        impl<const Q: $T> One for $Z<Q> {
            fn one() -> Self {
                Self { value: 1 }
            }
        }

        impl<const Q: $T> ConstOne for $Z<Q> {
            const ONE: Self = Self { value: 1 };
        }
    };
}

impl_one_zero_primitives!(i32, ZqI32);
impl_one_zero_primitives!(i64, ZqI64);
impl_one_zero_primitives!(u32, ZqU32);
impl_one_zero_primitives!(u64, ZqU64);
impl_one_zero_primitives!(i128, ZqI128);
impl_one_zero_primitives!(u128, ZqU128);
