//! Module implementing an Open Metrics gauge.
//!
//! See [`Gauge`] for details.

use crate::encoding::{EncodeGaugeValue, EncodeMetric, MetricEncoder};

use super::{MetricType, TypedMetric};

/// Open Metrics [`Gauge`] to record current measurements.
///
/// Single increasing, decreasing or constant value metric.
///
/// [`Gauge`] is generic over the actual data type tracking the [`Gauge`] state
/// as well as the data type used to interact with the [`Gauge`]. Out of
/// convenience the generic type parameters are set to use an [`AtomicI64`] as a
/// storage and [`i64`] on the interface by default.
///
/// # Examples
///
/// ## Using [`AtomicI64`] as storage and [`i64`] on the interface
///
/// ```
/// # use prometheus_client::metrics::gauge::Gauge;
/// let gauge: Gauge = Gauge::default();
/// gauge.set(42);
/// let _value = gauge.get();
/// ```
///
/// ## Using [`AtomicU64`] as storage and [`f64`] on the interface
///
/// ```
/// # use prometheus_client::metrics::gauge::Gauge;
/// # use std::sync::atomic::AtomicU64;
/// let gauge = Gauge::<f64, AtomicU64>::default();
/// gauge.set(42.0);
/// let _value: f64 = gauge.get();
/// ```
#[cfg(not(any(target_arch = "mips", target_arch = "powerpc")))]
#[derive(Debug)]
pub struct Gauge<N = i64> {
    value: N,
}

/// Open Metrics [`Gauge`] to record current measurements.
#[cfg(any(target_arch = "mips", target_arch = "powerpc"))]
#[derive(Debug)]
pub struct Gauge<N = i32> {
    value: N,
}

impl<N: Clone> Clone for Gauge<N> {
    fn clone(&self) -> Self {
        Self {
            value: self.value.clone(),
        }
    }
}

impl<N: Default> Default for Gauge<N> {
    fn default() -> Self {
        Self {
            value: N::default(),
        }
    }
}

impl<N: Number> Gauge<N> {
    /// Increase the [`Gauge`] by 1, returning the previous value.
    pub fn inc(&mut self) -> N {
        self.value.inc()
    }

    /// Increase the [`Gauge`] by `v`, returning the previous value.
    pub fn inc_by(&mut self, v: N) -> N {
        self.value.inc_by(v)
    }

    /// Decrease the [`Gauge`] by 1, returning the previous value.
    pub fn dec(&mut self) -> N {
        self.value.dec()
    }

    /// Decrease the [`Gauge`] by `v`, returning the previous value.
    pub fn dec_by(&mut self, v: N) -> N {
        self.value.dec_by(v)
    }

    /// Sets the [`Gauge`] to `v`, returning the previous value.
    pub fn set(&mut self, v: N) -> N {
        self.value.set(v)
    }

    /// Get the current value of the [`Gauge`].
    pub fn get(&self) -> N {
        self.value.get()
    }
}

/// Atomic operations for a [`Gauge`] value store.
pub trait Number {
    /// Increase the value by `1`.
    fn inc(&mut self) -> Self;

    /// Increase the value.
    fn inc_by(&mut self, v: Self) -> Self;

    /// Decrease the value by `1`.
    fn dec(&mut self) -> Self;

    /// Decrease the value.
    fn dec_by(&mut self, v: Self) -> Self;

    /// Set the value.
    fn set(&mut self, v: Self) -> Self;

    /// Get the value.
    fn get(&self) -> Self;
}

impl Number for i32 {
    fn inc(&mut self) -> i32 {
        self.inc_by(1)
    }

    fn inc_by(&mut self, v: i32) -> i32 {
        *self += v;
        *self
    }

    fn dec(&mut self) -> i32 {
        self.dec_by(1)
    }

    fn dec_by(&mut self, v: i32) -> i32 {
        *self -= v;
        *self
    }

    fn set(&mut self, v: i32) -> i32 {
        *self = v;
        *self
    }

    fn get(&self) -> i32 {
        *self
    }
}

impl Number for u32 {
    fn inc(&mut self) -> u32 {
        self.inc_by(1)
    }

    fn inc_by(&mut self, v: u32) -> u32 {
        *self += v;
        *self
    }

    fn dec(&mut self) -> u32 {
        self.dec_by(1)
    }

    fn dec_by(&mut self, v: u32) -> u32 {
        *self -= v;
        *self
    }

    fn set(&mut self, v: u32) -> u32 {
        *self = v;
        *self
    }

    fn get(&self) -> u32 {
        *self
    }
}

#[cfg(not(any(target_arch = "mips", target_arch = "powerpc")))]
impl Number for i64 {
    fn inc(&mut self) -> i64 {
        self.inc_by(1)
    }

    fn inc_by(&mut self, v: i64) -> i64 {
        *self += v;
        *self
    }

    fn dec(&mut self) -> i64 {
        self.dec_by(1)
    }

    fn dec_by(&mut self, v: i64) -> i64 {
        *self -= v;
        *self
    }

    fn set(&mut self, v: i64) -> i64 {
        *self = v;
        *self
    }

    fn get(&self) -> i64 {
        *self
    }
}

#[cfg(not(any(target_arch = "mips", target_arch = "powerpc")))]
impl Number for f64 {
    fn inc(&mut self) -> f64 {
        self.inc_by(1.0)
    }

    fn inc_by(&mut self, v: f64) -> f64 {
        *self += v;
        *self
    }

    fn dec(&mut self) -> f64 {
        self.dec_by(1.0)
    }

    fn dec_by(&mut self, v: f64) -> f64 {
        *self -= v;
        *self
    }

    fn set(&mut self, v: f64) -> f64 {
        *self = v;
        *self
    }

    fn get(&self) -> f64 {
        *self
    }
}

impl<N> TypedMetric for Gauge<N> {
    const TYPE: MetricType = MetricType::Gauge;
}

impl<N> EncodeMetric for Gauge<N>
where
    N: EncodeGaugeValue + Number,
{
    fn encode(&self, mut encoder: MetricEncoder) -> Result<(), std::fmt::Error> {
        encoder.encode_gauge(&self.get())
    }
    fn metric_type(&self) -> MetricType {
        Self::TYPE
    }
}

/// As a [`Gauge`], but constant, meaning it cannot change once created.
///
/// Needed for advanced use-cases, e.g. in combination with [`Collector`](crate::collector::Collector).
#[derive(Debug, Default)]
pub struct ConstGauge<N = i64> {
    value: N,
}

impl<N> ConstGauge<N> {
    /// Creates a new [`ConstGauge`].
    pub fn new(value: N) -> Self {
        Self { value }
    }
}

impl<N> TypedMetric for ConstGauge<N> {
    const TYPE: MetricType = MetricType::Gauge;
}

impl<N> EncodeMetric for ConstGauge<N>
where
    N: EncodeGaugeValue,
{
    fn encode(&self, mut encoder: MetricEncoder) -> Result<(), std::fmt::Error> {
        encoder.encode_gauge(&self.value)
    }

    fn metric_type(&self) -> MetricType {
        Self::TYPE
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn inc_dec_and_get() {
        let mut gauge: Gauge = Gauge::default();
        assert_eq!(0, gauge.inc());
        assert_eq!(1, gauge.get());

        assert_eq!(1, gauge.dec());
        assert_eq!(0, gauge.get());

        assert_eq!(0, gauge.set(10));
        assert_eq!(10, gauge.get());
    }
}
