/// A macro to create a vector of `ZqI32`. It transforms the following code:
///
/// ```ignore
/// zqi32_vec![1,2,3 ; Q]
/// ```
///
/// into
///
/// ```ignore
/// vec![ZqI32::<Q>::new(1), ZqI32::<Q>::new(2), ZqI32::<Q>::new(3)]
/// ```
///
/// Please note the semi-colon `;` is not for specifying the length of the vector (as vec! macro does),
/// but for specifying the value of the prime modulus Q.
#[macro_export]
macro_rules! zqi32_vec {
    ($($x:expr),* ; $Q:expr) => {{
        vec![ $($crate::zq::ZqI32::<$Q>::new($x)),* ]
    }};
}

/// A macro to create a vector of `ZqI64`. It transforms the following code:
///
/// ```ignore
/// zqi64_vec![1,2,3 ; Q]
/// ```
///
/// into
///
/// ```ignore
/// vec![ZqI64::<Q>::new(1), ZqI64::<Q>::new(2), ZqI64::<Q>::new(3)]
/// ```
///
/// Please note the semi-colon `;` is not for specifying the length of the vector (as vec! macro does),
/// but for specifying the value of the prime modulus Q.
#[macro_export]
macro_rules! zqi64_vec {
    ($($x:expr),* ; $Q:expr) => {{
        vec![ $($crate::zq::ZqI64::<$Q>::new($x)),* ]
    }};
}

/// A macro to create a vector of `ZqI128`. It transforms the following code:
///
/// ```ignore
/// zqi128_vec![1,2,3 ; Q]
/// ```
///
/// into
///
/// ```ignore
/// vec![ZqI128::<Q>::new(1), ZqI128::<Q>::new(2), ZqI128::<Q>::new(3)]
/// ```
///
/// Please note the semi-colon `;` is not for specifying the length of the vector (as vec! macro does),
/// but for specifying the value of the prime modulus Q.
#[macro_export]
macro_rules! zqi128_vec {
    ($($x:expr),* ; $Q:expr) => {{
        vec![ $($crate::zq::ZqI128::<$Q>::new($x)),* ]
    }};
}

/// A macro to create a vector of `ZqU32`. It transforms the following code:
///
/// ```ignore
/// zqu32_vec![1,2,3 ; Q]
/// ```
///
/// into
///
/// ```ignore
/// vec![ZqU32::<Q>::new(1), ZqU32::<Q>::new(2), ZqU32::<Q>::new(3)]
/// ```
///
/// Please note the semi-colon `;` is not for specifying the length of the vector (as vec! macro does),
/// but for specifying the value of the prime modulus Q.
#[macro_export]
macro_rules! zqu32_vec {
    ($($x:expr),* ; $Q:expr) => {{
        vec![ $($crate::zq::ZqU32::<$Q>::new($x)),* ]
    }};
}

/// A macro to create a vector of `ZqU64`. It transforms the following code:
///
/// ```ignore
/// zqu64_vec![1,2,3 ; Q]
/// ```
///
/// into
///
/// ```ignore
/// vec![ZqU64::<Q>::new(1), ZqU64::<Q>::new(2), ZqU64::<Q>::new(3)]
/// ```
///
/// Please note the semi-colon `;` is not for specifying the length of the vector (as vec! macro does),
/// but for specifying the value of the prime modulus Q.
#[macro_export]
macro_rules! zqu64_vec {
    ($($x:expr),* ; $Q:expr) => {{
        vec![ $($crate::zq::ZqU64::<$Q>::new($x)),* ]
    }};
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_zqi32_vec() {
        let v = zqi32_vec![-9, -6, 0, 6; 7];
        let values = v.iter().map(|x| x.value).collect::<Vec<_>>();
        assert_eq!(values, vec![-2, 1, 0, -1]);
    }

    #[test]
    fn test_zqi64_vec() {
        let v = zqi64_vec![-9, -6, 0, 6; 7];
        let values = v.iter().map(|x| x.value).collect::<Vec<_>>();
        assert_eq!(values, vec![-2, 1, 0, -1]);
    }

    #[test]
    fn test_zqi128_vec() {
        let v = zqi128_vec![-9, -6, 0, 6; 7];
        let values = v.iter().map(|x| x.value).collect::<Vec<_>>();
        assert_eq!(values, vec![-2, 1, 0, -1]);
    }

    #[test]
    fn test_zqu32_vec() {
        let v = zqu32_vec![12, 8, 0, 6; 7];
        let values = v.iter().map(|x| x.value).collect::<Vec<_>>();
        assert_eq!(values, vec![5, 1, 0, 6]);
    }

    #[test]
    fn test_zqu64_vec() {
        let v = zqu64_vec![12, 8, 0, 6; 7];
        let values = v.iter().map(|x| x.value).collect::<Vec<_>>();
        assert_eq!(values, vec![5, 1, 0, 6]);
    }
}
