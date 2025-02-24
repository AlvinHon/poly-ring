use rand::distr::{
    uniform::{SampleUniform, UniformInt, UniformSampler},
    Distribution, StandardUniform,
};

use super::{ZqI32, ZqI64, ZqU32, ZqU64};

macro_rules! sampler_structs_uniform_impls {
    ($S:tt, $T:ty, $Z:tt) => {
        pub struct $S<const Q: $T>(UniformInt<$T>);

        impl<const Q: $T> UniformSampler for $S<Q> {
            type X = $Z<Q>;

            fn new<B1, B2>(low: B1, high: B2) -> Result<Self, rand::distr::uniform::Error>
            where
                B1: rand::distr::uniform::SampleBorrow<Self::X> + Sized,
                B2: rand::distr::uniform::SampleBorrow<Self::X> + Sized,
            {
                UniformInt::<$T>::new(low.borrow().value, high.borrow().value).map($S)
            }

            fn new_inclusive<B1, B2>(low: B1, high: B2) -> Result<Self, rand::distr::uniform::Error>
            where
                B1: rand::distr::uniform::SampleBorrow<Self::X> + Sized,
                B2: rand::distr::uniform::SampleBorrow<Self::X> + Sized,
            {
                UniformSampler::new(low, high)
            }

            fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> Self::X {
                $Z::<Q>::new(self.0.sample(rng))
            }
        }

        impl<const Q: $T> SampleUniform for $Z<Q> {
            type Sampler = $S<Q>;
        }

        impl<const Q: $T> Distribution<$Z<Q>> for StandardUniform {
            fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> $Z<Q> {
                $Z::<Q>::new(self.sample(rng))
            }
        }
    };
}

sampler_structs_uniform_impls!(ZqI32Sampler, i32, ZqI32);
sampler_structs_uniform_impls!(ZqI64Sampler, i64, ZqI64);
sampler_structs_uniform_impls!(ZqU32Sampler, u32, ZqU32);
sampler_structs_uniform_impls!(ZqU64Sampler, u64, ZqU64);

#[cfg(test)]
mod tests {
    use rand::Rng;

    use super::*;

    #[test]
    fn test_zqi32_sampler() {
        let rng = &mut rand::rng();
        let start = ZqI32::<7>::new(-2);
        let end = ZqI32::<7>::new(2);
        let range = start.clone()..=end.clone();
        let x = rng.random_range(range);
        assert!(x >= start);
        assert!(x <= end);
    }

    #[test]
    fn test_zqi64_sampler() {
        let rng = &mut rand::rng();
        let start = ZqI64::<7>::new(-2);
        let end = ZqI64::<7>::new(2);
        let range = start.clone()..=end.clone();
        let x = rng.random_range(range);
        assert!(x >= start);
        assert!(x <= end);
    }

    #[test]
    fn test_zqu32_sampler() {
        let rng = &mut rand::rng();
        let start = ZqU32::<7>::new(2);
        let end = ZqU32::<7>::new(5);
        let range = start.clone()..=end.clone();
        let x = rng.random_range(range);
        assert!(x >= start);
        assert!(x <= end);
    }

    #[test]
    fn test_zqu64_sampler() {
        let rng = &mut rand::rng();
        let start = ZqU64::<7>::new(2);
        let end = ZqU64::<7>::new(5);
        let range = start.clone()..=end.clone();
        let x = rng.random_range(range);
        assert!(x >= start);
        assert!(x <= end);
    }
}
