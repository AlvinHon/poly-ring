use serde::{Deserialize, Serialize};

use super::{ZqI32, ZqI64, ZqU32, ZqU64};

macro_rules! impl_serde_for_zq {
    ($T:ty, $Z:tt) => {
        impl<const Q: $T> Serialize for $Z<Q> {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: serde::Serializer,
            {
                self.value.serialize(serializer)
            }
        }

        impl<'de, const Q: $T> Deserialize<'de> for $Z<Q> {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: serde::Deserializer<'de>,
            {
                let value = <$T>::deserialize(deserializer)?;
                Ok(Self::new(value))
            }
        }
    };
}

impl_serde_for_zq!(i32, ZqI32);
impl_serde_for_zq!(i64, ZqI64);
impl_serde_for_zq!(u32, ZqU32);
impl_serde_for_zq!(u64, ZqU64);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_zqi32_serde() {
        let z = ZqI32::<7>::new(3);
        let serialized_z = bincode::serialize(&z).unwrap();
        assert_eq!(serialized_z.len(), 4);

        let deserialized_z = bincode::deserialize(&serialized_z).unwrap();
        assert_eq!(z, deserialized_z);
    }

    #[test]
    fn test_zqi64_serde() {
        let z = ZqI64::<7>::new(3);
        let serialized_z = bincode::serialize(&z).unwrap();
        assert_eq!(serialized_z.len(), 8);

        let deserialized_z = bincode::deserialize(&serialized_z).unwrap();
        assert_eq!(z, deserialized_z);
    }

    #[test]
    fn test_zqu32_serde() {
        let z = ZqU32::<7>::new(3);
        let serialized_z = bincode::serialize(&z).unwrap();
        assert_eq!(serialized_z.len(), 4);

        let deserialized_z = bincode::deserialize(&serialized_z).unwrap();
        assert_eq!(z, deserialized_z);
    }

    #[test]
    fn test_zqu64_serde() {
        let z = ZqU64::<7>::new(3);
        let serialized_z = bincode::serialize(&z).unwrap();
        assert_eq!(serialized_z.len(), 8);

        let deserialized_z = bincode::deserialize(&serialized_z).unwrap();
        assert_eq!(z, deserialized_z);
    }
}
