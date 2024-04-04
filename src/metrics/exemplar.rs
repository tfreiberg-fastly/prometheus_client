//! Module implementing an Open Metrics exemplars for counters and histograms.
//!
//! See [`CounterWithExemplar`] and [`HistogramWithExemplars`] for details.

use crate::encoding::{
    EncodeCounterValue, EncodeExemplarValue, EncodeLabelSet, EncodeMetric, MetricEncoder,
};

use super::counter::{self, Counter};
use super::histogram::Histogram;
use super::{MetricType, TypedMetric};
use std::collections::HashMap;

/// An OpenMetrics exemplar.
#[derive(Debug, Clone)]
pub struct Exemplar<S, V> {
    pub(crate) label_set: S,
    pub(crate) value: V,
}

/////////////////////////////////////////////////////////////////////////////////
// Counter

/// Open Metrics [`Counter`] with an [`Exemplar`] to both measure discrete
/// events and track references to data outside of the metric set.
///
/// ```
/// # use prometheus_client::metrics::exemplar::CounterWithExemplar;
/// let counter_with_exemplar = CounterWithExemplar::<Vec<(String, String)>>::default();
/// counter_with_exemplar.inc_by(1, Some(vec![("user_id".to_string(), "42".to_string())]));
/// let _value: (u64, _) = counter_with_exemplar.get();
/// ```
/// You can also use exemplars with families. Just wrap the exemplar in a Family.
/// ```
/// # use prometheus_client::metrics::exemplar::CounterWithExemplar;
/// # use prometheus_client::metrics::histogram::exponential_buckets;
/// # use prometheus_client::metrics::family::Family;
/// # use prometheus_client_derive_encode::EncodeLabelSet;
/// #[derive(Clone, Hash, PartialEq, Eq, EncodeLabelSet, Debug, Default)]
/// pub struct ResultLabel {
///     pub result: String,
/// }
///
/// #[derive(Clone, Hash, PartialEq, Eq, EncodeLabelSet, Debug, Default)]
/// pub struct TraceLabel {
///     pub trace_id: String,
/// }
///
/// let latency: Family<ResultLabel, CounterWithExemplar<TraceLabel>> = Family::default();
///
/// latency
///     .get_or_create(&ResultLabel {
///         result: "success".to_owned(),
///     })
///     .inc_by(
///         1,
///         Some(TraceLabel {
///             trace_id: "3a2f90c9f80b894f".to_owned(),
///         }),
///     );
/// ```
#[cfg(not(any(target_arch = "mips", target_arch = "powerpc")))]
#[derive(Debug, Clone, Default)]
pub struct CounterWithExemplar<S, N = u64> {
    pub(crate) exemplar: Option<Exemplar<S, N>>,
    pub(crate) counter: Counter<N>,
}

impl<S> TypedMetric for CounterWithExemplar<S> {
    const TYPE: MetricType = MetricType::Counter;
}

/// Open Metrics [`Counter`] with an [`Exemplar`] to both measure discrete
/// events and track references to data outside of the metric set.
#[cfg(any(target_arch = "mips", target_arch = "powerpc"))]
#[derive(Debug, Clone)]
pub struct CounterWithExemplar<S, N = u32> {
    pub(crate) exemplar: Option<Exemplar<S, N>>,
    pub(crate) counter: Counter<N>,
}

impl<S, N: Clone + counter::Number> CounterWithExemplar<S, N> {
    // TODO: Implement `fn inc`. Problematic right now as one can not produce
    // value `1` of type `N`.

    /// Increase the [`CounterWithExemplar`] by `v`, updating the [`Exemplar`]
    /// if a label set is provided, returning the previous value.
    pub fn inc_by(&mut self, v: N, label_set: Option<S>) -> N {
        self.exemplar = label_set.map(|label_set| Exemplar {
            label_set,
            value: v.clone(),
        });

        self.counter.inc_by(v)
    }

    /// Get the current value of the [`CounterWithExemplar`] as well as its
    /// [`Exemplar`] if any.
    pub fn get(&self) -> (N, &Option<Exemplar<S, N>>) {
        let value = self.counter.get();
        let exemplar = &self.exemplar;
        (value, exemplar)
    }
}

// TODO: S, V, N, A are hard to grasp.
impl<S, N> EncodeMetric for crate::metrics::exemplar::CounterWithExemplar<S, N>
where
    S: EncodeLabelSet,
    N: EncodeCounterValue + EncodeExemplarValue + Clone + counter::Number,
{
    fn encode(&self, mut encoder: MetricEncoder) -> Result<(), std::fmt::Error> {
        let (value, exemplar) = self.get();
        encoder.encode_counter(&value, exemplar.as_ref())
    }

    fn metric_type(&self) -> MetricType {
        Counter::<N>::TYPE
    }
}

/////////////////////////////////////////////////////////////////////////////////
// Histogram

/// Open Metrics [`Histogram`] to both measure distributions of discrete events.
/// and track references to data outside of the metric set.
///
/// ```
/// # use prometheus_client::metrics::exemplar::HistogramWithExemplars;
/// # use prometheus_client::metrics::histogram::exponential_buckets;
/// let histogram = HistogramWithExemplars::new(exponential_buckets(1.0, 2.0, 10));
/// histogram.observe(4.2, Some(vec![("user_id".to_string(), "42".to_string())]));
/// ```
/// You can also use exemplars with families. Just wrap the exemplar in a Family.
/// ```
/// # use prometheus_client::metrics::exemplar::HistogramWithExemplars;
/// # use prometheus_client::metrics::histogram::exponential_buckets;
/// # use prometheus_client::metrics::family::Family;
/// # use prometheus_client::encoding::EncodeLabelSet;
/// #[derive(Clone, Hash, PartialEq, Eq, EncodeLabelSet, Debug, Default)]
/// pub struct ResultLabel {
///     pub result: String,
/// }
///
/// #[derive(Clone, Hash, PartialEq, Eq, EncodeLabelSet, Debug, Default)]
/// pub struct TraceLabel {
///     pub trace_id: String,
/// }
///
/// let latency: Family<ResultLabel, HistogramWithExemplars<TraceLabel>> =
///     Family::new_with_constructor(|| {
///         HistogramWithExemplars::new(exponential_buckets(1.0, 2.0, 10))
///     });
///
/// latency
///     .get_or_create(&ResultLabel {
///         result: "success".to_owned(),
///     })
///     .observe(
///         0.001345422,
///         Some(TraceLabel {
///             trace_id: "3a2f90c9f80b894f".to_owned(),
///         }),
///     );
/// ```
#[derive(Debug, Clone)]
pub struct HistogramWithExemplars<S> {
    pub(crate) exemplars: HashMap<usize, Exemplar<S, f64>>,
    pub(crate) histogram: Histogram,
}

impl<S> TypedMetric for HistogramWithExemplars<S> {
    const TYPE: MetricType = MetricType::Histogram;
}

impl<S> HistogramWithExemplars<S> {
    /// Create a new [`HistogramWithExemplars`].
    pub fn new(buckets: impl Iterator<Item = f64>) -> Self {
        Self {
            exemplars: Default::default(),
            histogram: Histogram::new(buckets),
        }
    }

    /// Observe the given value, optionally providing a label set and thus
    /// setting the [`Exemplar`] value.
    pub fn observe(&mut self, v: f64, label_set: Option<S>) {
        let bucket = self.histogram.observe_and_bucket(v);
        if let (Some(bucket), Some(label_set)) = (bucket, label_set) {
            self.exemplars.insert(
                bucket,
                Exemplar {
                    label_set,
                    value: v,
                },
            );
        }
    }
}

impl<S: EncodeLabelSet> EncodeMetric for HistogramWithExemplars<S> {
    fn encode(&self, mut encoder: MetricEncoder) -> Result<(), std::fmt::Error> {
        let (sum, count, buckets) = self.histogram.get();
        encoder.encode_histogram(sum, count, &buckets, Some(&self.exemplars))
    }

    fn metric_type(&self) -> MetricType {
        Histogram::TYPE
    }
}
