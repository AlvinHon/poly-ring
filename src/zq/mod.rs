pub mod bytes;
pub mod cast;
pub mod inv;
pub mod macros;
pub mod ops;
#[cfg(feature = "rand")]
pub mod rand;
#[cfg(feature = "serde")]
pub mod serde;

/// A type representing an element of the ring Z/QZ. The value is normalized to the range \[-Q/2, Q/2\).
///
/// ## Safety
/// Q should be an odd prime number. Although the primality of Q is not checked in the implementation,
/// its implementation makes this assumption for achieving some important properties of ring Z/QZ.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ZqI32<const Q: i32> {
    pub(crate) value: i32,
}

impl<const Q: i32> ZqI32<Q> {
    /// Creates a new `ZqI32` from the given value. It normalizes the value to the range \[-Q/2, Q/2\).
    pub fn new(value: i32) -> Self {
        let a = value.rem_euclid(Q);
        if a > Q / 2 {
            Self { value: a - Q }
        } else {
            Self { value: a }
        }
    }

    pub(crate) fn safe_new(value: num::BigInt) -> Self {
        use num::ToPrimitive;
        let a = value.to_i64().unwrap().rem_euclid(Q as i64) as i32;
        if a > Q / 2 {
            Self { value: a - Q }
        } else {
            Self { value: a }
        }
    }
}

/// A type representing an element of the ring Z/QZ. The value is normalized to the range \[-Q/2, Q/2\).
///
/// ## Safety
/// Q should be an odd prime number. Although the primality of Q is not checked in the implementation,
/// its implementation makes this assumption for achieving some important properties of ring Z/QZ.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ZqI64<const Q: i64> {
    pub(crate) value: i64,
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

    fn safe_new(value: num::BigInt) -> Self {
        use num::ToPrimitive;
        let a = value.to_i128().unwrap().rem_euclid(Q as i128) as i64;
        if a > Q / 2 {
            Self { value: a - Q }
        } else {
            Self { value: a }
        }
    }
}

/// A type representing an element of the ring Z/QZ.
///
/// ## Safety
/// Q should be an odd prime number. Although the primality of Q is not checked in the implementation,
/// its implementation makes this assumption for achieving some important properties of ring Z/QZ.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ZqU32<const Q: u32> {
    pub(crate) value: u32,
}

impl<const Q: u32> ZqU32<Q> {
    /// Creates a new `ZqU32` from the given value.
    pub fn new(value: u32) -> Self {
        Self {
            value: value.rem_euclid(Q),
        }
    }

    pub(crate) fn safe_new(value: num::BigInt) -> Self {
        use num::ToPrimitive;
        Self {
            value: value.to_u64().unwrap().rem_euclid(Q as u64) as u32,
        }
    }
}

/// A type representing an element of the ring Z/QZ.
///
/// ## Safety
/// Q should be an odd prime number. Although the primality of Q is not checked in the implementation,
/// its implementation makes this assumption for achieving some important properties of ring Z/QZ.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ZqU64<const Q: u64> {
    pub(crate) value: u64,
}

impl<const Q: u64> ZqU64<Q> {
    /// Creates a new `ZqU64` from the given value.
    pub fn new(value: u64) -> Self {
        Self {
            value: value.rem_euclid(Q),
        }
    }

    pub(crate) fn safe_new(value: num::BigInt) -> Self {
        use num::ToPrimitive;
        Self {
            value: value.to_u128().unwrap().rem_euclid(Q as u128) as u64,
        }
    }
}

macro_rules! impl_change_moduus {
    ($T:ty,  $Z:tt) => {
        impl<const Q: $T> $Z<Q> {
            pub fn change_modulus<const Q2: $T>(&self) -> $Z<Q2> {
                $Z::<Q2>::new(self.value)
            }
        }
    };
}

impl_change_moduus!(i32, ZqI32);
impl_change_moduus!(i64, ZqI64);
impl_change_moduus!(u32, ZqU32);
impl_change_moduus!(u64, ZqU64);

#[cfg(test)]
mod change_modulus_tests {
    use super::*;

    #[test]
    fn test_change_modulus() {
        let zq = ZqI32::<7>::new(3);
        assert_eq!(zq.change_modulus::<5>(), ZqI32::<5>::new(3));

        let zq = ZqI32::<7>::new(-3);
        assert_eq!(zq.change_modulus::<5>(), ZqI32::<5>::new(2));

        let zq = ZqI64::<7>::new(3);
        assert_eq!(zq.change_modulus::<5>(), ZqI64::<5>::new(3));

        let zq = ZqI64::<7>::new(-3);
        assert_eq!(zq.change_modulus::<5>(), ZqI64::<5>::new(2));

        let zq = ZqU32::<7>::new(3);
        assert_eq!(zq.change_modulus::<5>(), ZqU32::<5>::new(3));

        let zq = ZqU32::<7>::new(10);
        assert_eq!(zq.change_modulus::<5>(), ZqU32::<5>::new(3));

        let zq = ZqU64::<7>::new(3);
        assert_eq!(zq.change_modulus::<5>(), ZqU64::<5>::new(3));

        let zq = ZqU64::<7>::new(10);
        assert_eq!(zq.change_modulus::<5>(), ZqU64::<5>::new(3));
    }
}
