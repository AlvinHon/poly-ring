use std::ops::Neg;

use num::{One, Signed, Zero};

use crate::zq::{ZqI128, ZqI32, ZqI64};

macro_rules! impl_signed {
    ($T:ty,  $Z:tt) => {
        impl<const Q: $T> Signed for $Z<Q> {
            fn abs(&self) -> Self {
                if self.is_negative() {
                    self.neg()
                } else {
                    self.clone()
                }
            }

            fn abs_sub(&self, other: &Self) -> Self {
                if self > other {
                    self - other
                } else {
                    Self::zero()
                }
            }

            fn signum(&self) -> Self {
                if self.is_zero() {
                    Self::zero()
                } else if self.is_negative() {
                    Self::one().neg()
                } else {
                    Self::one()
                }
            }

            fn is_positive(&self) -> bool {
                self > &Self::zero()
            }

            fn is_negative(&self) -> bool {
                self < &Self::zero()
            }
        }
    };
}

impl_signed!(i32, ZqI32);
impl_signed!(i64, ZqI64);
impl_signed!(i128, ZqI128);

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_signed() {
        let zq = ZqI32::<7>::new(3);
        assert!(zq.is_positive());
        assert!(!zq.is_negative());
        assert_eq!(zq.abs(), zq);
        assert_eq!(zq.signum(), ZqI32::<7>::new(1));

        let zq = ZqI32::<7>::new(-3);
        assert!(!zq.is_positive());
        assert!(zq.is_negative());
        assert_eq!(zq.abs(), ZqI32::<7>::new(3));
        assert_eq!(zq.signum(), ZqI32::<7>::new(-1));

        let zq = ZqI32::<7>::new(0);
        assert!(!zq.is_positive());
        assert!(!zq.is_negative());
        assert_eq!(zq.abs(), zq);
        assert_eq!(zq.signum(), ZqI32::<7>::new(0));
    }
}
