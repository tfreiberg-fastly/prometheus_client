//! Module implementing an Open Metrics histogram.
//!
//! See [`Histogram`] for details.

use crate::encoding::{EncodeMetric, MetricEncoder};

use super::{MetricType, TypedMetric};
use std::iter::{self, once};

/// Open Metrics [`Histogram`] to measure distributions of discrete events.
///
/// ```
/// # use prometheus_client::metrics::histogram::{Histogram, exponential_buckets};
/// let histogram = Histogram::new(exponential_buckets(1.0, 2.0, 10));
/// histogram.observe(4.2);
/// ```
///
/// [`Histogram`] does not implement [`Default`], given that the choice of
/// bucket values depends on the situation [`Histogram`] is used in. As an
/// example, to measure HTTP request latency, the values suggested in the
/// Golang implementation might work for you:
///
/// ```
/// # use prometheus_client::metrics::histogram::Histogram;
/// // Default values from go client(https://github.com/prometheus/client_golang/blob/5d584e2717ef525673736d72cd1d12e304f243d7/prometheus/histogram.go#L68)
/// let custom_buckets = [
///    0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1.0, 2.5, 5.0, 10.0,
/// ];
/// let histogram = Histogram::new(custom_buckets.into_iter());
/// histogram.observe(4.2);
/// ```
// TODO: Consider using atomics. See
// https://github.com/tikv/rust-prometheus/pull/314.
#[derive(Clone, Debug)]
pub struct Histogram {
    // TODO: Consider allowing integer observe values.
    sum: f64,
    count: u64,
    // TODO: Consider being generic over the bucket length.
    buckets: Vec<(f64, u64)>,
}

#[derive(Debug)]
pub(crate) struct Inner {}

impl Histogram {
    /// Create a new [`Histogram`].
    pub fn new(buckets: impl Iterator<Item = f64>) -> Self {
        Self {
            sum: Default::default(),
            count: Default::default(),
            buckets: buckets
                .into_iter()
                .chain(once(f64::MAX))
                .map(|upper_bound| (upper_bound, 0))
                .collect(),
        }
    }

    /// Number observed values
    pub fn count(&self) -> u64 {
        self.count
    }

    /// Observe the given value.
    pub fn observe(&mut self, v: f64) {
        self.observe_and_bucket(v);
    }

    /// Sum of observed values
    pub fn sum(&self) -> f64 {
        self.sum
    }

    /// Observes the given value, returning the index of the first bucket the
    /// value is added to.
    ///
    /// Needed in
    /// [`HistogramWithExemplars`](crate::metrics::exemplar::HistogramWithExemplars).
    pub(crate) fn observe_and_bucket(&mut self, v: f64) -> Option<usize> {
        self.sum += v;
        self.count += 1;

        let first_bucket = self
            .buckets
            .iter_mut()
            .enumerate()
            .find(|(_i, (upper_bound, _value))| upper_bound >= &v);

        match first_bucket {
            Some((i, (_upper_bound, value))) => {
                *value += 1;
                Some(i)
            }
            None => None,
        }
    }

    pub(crate) fn get(&self) -> (f64, u64, &[(f64, u64)]) {
        (self.sum, self.count, &self.buckets)
    }
}

impl TypedMetric for Histogram {
    const TYPE: MetricType = MetricType::Histogram;
}

/// Exponential bucket distribution.
pub fn exponential_buckets(start: f64, factor: f64, length: u16) -> impl Iterator<Item = f64> {
    iter::repeat(())
        .enumerate()
        .map(move |(i, _)| start * factor.powf(i as f64))
        .take(length.into())
}

/// Linear bucket distribution.
pub fn linear_buckets(start: f64, width: f64, length: u16) -> impl Iterator<Item = f64> {
    iter::repeat(())
        .enumerate()
        .map(move |(i, _)| start + (width * (i as f64)))
        .take(length.into())
}

impl EncodeMetric for Histogram {
    fn encode(&self, mut encoder: MetricEncoder) -> Result<(), std::fmt::Error> {
        let (sum, count, buckets) = self.get();
        encoder.encode_histogram::<()>(sum, count, &buckets, None)
    }

    fn metric_type(&self) -> MetricType {
        Self::TYPE
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn histogram() {
        let mut histogram = Histogram::new(exponential_buckets(1.0, 2.0, 10));
        histogram.observe(1.0);
        histogram.observe(2.0);

        assert_eq!(2, histogram.count());
        assert_eq!(3.0, histogram.sum());
    }

    #[test]
    fn exponential() {
        assert_eq!(
            vec![1.0, 2.0, 4.0, 8.0, 16.0, 32.0, 64.0, 128.0, 256.0, 512.0],
            exponential_buckets(1.0, 2.0, 10).collect::<Vec<_>>()
        );
    }

    #[test]
    fn linear() {
        assert_eq!(
            vec![0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0],
            linear_buckets(0.0, 1.0, 10).collect::<Vec<_>>()
        );
    }
}
