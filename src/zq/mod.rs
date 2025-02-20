pub mod i32;
pub use i32::ZqI32;
pub mod i64;
pub use i64::ZqI64;
pub mod u32;
pub use u32::ZqU32;
pub mod u64;
pub use u64::ZqU64;
pub mod bytes;

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
