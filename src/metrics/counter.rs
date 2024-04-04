//! Module implementing an Open Metrics counter.
//!
//! See [`Counter`] for details.

use crate::encoding::{EncodeMetric, MetricEncoder};

use super::{MetricType, TypedMetric};

/// Open Metrics [`Counter`] to measure discrete events.
///
/// Single monotonically increasing value metric.
///
/// [`Counter`] is generic over the actual data type tracking the [`Counter`]
/// state as well as the data type used to interact with the [`Counter`]. Out of
/// convenience the generic type parameters are set to use an [`AtomicU64`] as a
/// storage and [`u64`] on the interface by default.
///
/// # Examples
///
/// ## Using [`AtomicU64`] as storage and [`u64`] on the interface
///
/// ```
/// # use prometheus_client::metrics::counter::Counter;
/// let counter: Counter = Counter::default();
/// counter.inc();
/// let _value: u64 = counter.get();
/// ```
///
/// ## Using [`AtomicU64`] as storage and [`f64`] on the interface
///
/// ```
/// # use prometheus_client::metrics::counter::Counter;
/// # use std::sync::atomic::AtomicU64;
/// let counter = Counter::<f64, AtomicU64>::default();
/// counter.inc();
/// let _value: f64 = counter.get();
/// ```
#[cfg(not(any(target_arch = "mips", target_arch = "powerpc")))]
#[derive(Debug)]
pub struct Counter<N = u64> {
    value: N,
}

/// Open Metrics [`Counter`] to measure discrete events.
#[cfg(any(target_arch = "mips", target_arch = "powerpc"))]
#[derive(Debug)]
pub struct Counter<N = u32> {
    value: N,
}

impl<N: Clone> Clone for Counter<N> {
    fn clone(&self) -> Self {
        Self {
            value: self.value.clone(),
        }
    }
}

impl<N: Default> Default for Counter<N> {
    fn default() -> Self {
        Counter {
            value: N::default(),
        }
    }
}

impl<N: Number> Counter<N> {
    /// Increase the [`Counter`] by 1, returning the previous value.
    pub fn inc(&mut self) -> N {
        self.value.inc()
    }

    /// Increase the [`Counter`] by `v`, returning the previous value.
    pub fn inc_by(&mut self, v: N) -> N {
        self.value.inc_by(v)
    }

    /// Get the current value of the [`Counter`].
    pub fn get(&self) -> N {
        self.value.get()
    }
}

/// Atomic operations for a [`Counter`] value store.
pub trait Number {
    /// Increase the value by `1`.
    fn inc(&mut self) -> Self;

    /// Increase the value.
    fn inc_by(&mut self, v: Self) -> Self;

    /// Get the the value.
    fn get(&self) -> Self;
}

#[cfg(not(any(target_arch = "mips", target_arch = "powerpc")))]
impl Number for u64 {
    fn inc(&mut self) -> u64 {
        *self += 1;
        *self
    }

    fn inc_by(&mut self, v: u64) -> u64 {
        *self += v;
        *self
    }

    fn get(&self) -> u64 {
        *self
    }
}

impl Number for u32 {
    fn inc(&mut self) -> u32 {
        *self += 1;
        *self
    }

    fn inc_by(&mut self, v: u32) -> u32 {
        *self += v;
        *self
    }

    fn get(&self) -> u32 {
        *self
    }
}

#[cfg(not(any(target_arch = "mips", target_arch = "powerpc")))]
impl Number for f64 {
    fn inc(&mut self) -> f64 {
        *self += 1.0;
        *self
    }

    fn inc_by(&mut self, v: f64) -> f64 {
        *self += v;
        *self
    }

    fn get(&self) -> f64 {
        *self
    }
}

impl<N> TypedMetric for Counter<N> {
    const TYPE: MetricType = MetricType::Counter;
}

impl<N> EncodeMetric for Counter<N>
where
    N: crate::encoding::EncodeCounterValue + Number,
{
    fn encode(&self, mut encoder: MetricEncoder) -> Result<(), std::fmt::Error> {
        encoder.encode_counter::<(), _, u64>(&self.get(), None)
    }

    fn metric_type(&self) -> MetricType {
        Self::TYPE
    }
}

/// As a [`Counter`], but constant, meaning it cannot change once created.
///
/// Needed for advanced use-cases, e.g. in combination with [`Collector`](crate::collector::Collector).
#[derive(Debug, Default)]
pub struct ConstCounter<N = u64> {
    value: N,
}

impl<N> ConstCounter<N> {
    /// Creates a new [`ConstCounter`].
    pub fn new(value: N) -> Self {
        Self { value }
    }
}

impl<N> TypedMetric for ConstCounter<N> {
    const TYPE: MetricType = MetricType::Counter;
}

impl<N> EncodeMetric for ConstCounter<N>
where
    N: crate::encoding::EncodeCounterValue,
{
    fn encode(&self, mut encoder: MetricEncoder) -> Result<(), std::fmt::Error> {
        encoder.encode_counter::<(), _, u64>(&self.value, None)
    }

    fn metric_type(&self) -> MetricType {
        Self::TYPE
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quickcheck::QuickCheck;

    #[test]
    fn inc_and_get() {
        let mut counter: Counter = Counter::default();
        assert_eq!(0, counter.inc());
        assert_eq!(1, counter.get());
    }

    #[cfg(not(any(target_arch = "mips", target_arch = "powerpc")))]
    #[test]
    fn f64_stored_in_atomic_u64() {
        fn prop(fs: Vec<f64>) {
            let fs: Vec<f64> = fs
                .into_iter()
                // Map infinite, subnormal and NaN to 0.0.
                .map(|f| if f.is_normal() { f } else { 0.0 })
                .collect();
            let sum: f64 = fs.iter().sum();
            let mut counter = Counter::<f64>::default();
            for f in fs {
                counter.inc_by(f);
            }
            assert_eq!(counter.get(), sum)
        }

        QuickCheck::new().tests(10).quickcheck(prop as fn(_))
    }
}
