//! Module implementing an Open Metrics metric family.
//!
//! See [`Family`] for details.

use crate::encoding::{EncodeLabelSet, EncodeMetric, MetricEncoder};

use super::{MetricType, TypedMetric};
use parking_lot::{MappedRwLockReadGuard, RwLock, RwLockReadGuard, RwLockWriteGuard};
use std::sync::Arc;
use std::{
    collections::HashMap,
    hash::{BuildHasher, RandomState},
};

/// Representation of the OpenMetrics *MetricFamily* data type.
///
/// A [`Family`] is a set of metrics with the same name, help text and
/// type, differentiated by their label values thus spanning a multidimensional
/// space.
///
/// # Generic over the label set
///
/// A [`Family`] is generic over the label type. For convenience one might
/// choose a `Vec<(String, String)>`, for performance and/or type safety one might
/// define a custom type.
///
/// ## Examples
///
/// ### [`Family`] with `Vec<(String, String)>` for convenience
///
/// ```
/// # use prometheus_client::encoding::text::encode;
/// # use prometheus_client::metrics::counter::{Atomic, Counter};
/// # use prometheus_client::metrics::family::Family;
/// # use prometheus_client::registry::Registry;
/// #
/// # let mut registry = Registry::default();
/// let family = Family::<Vec<(String, String)>, Counter>::default();
/// # registry.register(
/// #   "my_counter",
/// #   "This is my counter",
/// #   family.clone(),
/// # );
///
/// // Record a single HTTP GET request.
/// family.get_or_create(&vec![("method".to_owned(), "GET".to_owned())]).inc();
///
/// # // Encode all metrics in the registry in the text format.
/// # let mut buffer = String::new();
/// # encode(&mut buffer, &registry).unwrap();
/// #
/// # let expected = "# HELP my_counter This is my counter.\n".to_owned() +
/// #                "# TYPE my_counter counter\n" +
/// #                "my_counter_total{method=\"GET\"} 1\n" +
/// #                "# EOF\n";
/// # assert_eq!(expected, buffer);
/// ```
///
/// ### [`Family`] with custom type for performance and/or type safety
///
/// Using `EncodeLabelSet` and `EncodeLabelValue` derive macro to generate
/// [`EncodeLabelSet`] for `struct`s and
/// [`EncodeLabelValue`](crate::encoding::EncodeLabelValue) for `enum`s.
///
/// ```
/// # use prometheus_client::encoding::{EncodeLabelSet, EncodeLabelValue};
/// # use prometheus_client::encoding::text::encode;
/// # use prometheus_client::metrics::counter::{Atomic, Counter};
/// # use prometheus_client::metrics::family::Family;
/// # use prometheus_client::registry::Registry;
/// # use std::io::Write;
/// #
/// # let mut registry = Registry::default();
/// #[derive(Clone, Debug, Hash, PartialEq, Eq, EncodeLabelSet)]
/// struct Labels {
///   method: Method,
/// };
///
/// #[derive(Clone, Debug, Hash, PartialEq, Eq, EncodeLabelValue)]
/// enum Method {
///   GET,
///   PUT,
/// };
///
/// let family = Family::<Labels, Counter>::default();
/// # registry.register(
/// #   "my_counter",
/// #   "This is my counter",
/// #   family.clone(),
/// # );
///
/// // Record a single HTTP GET request.
/// family.get_or_create(&Labels { method: Method::GET }).inc();
/// #
/// # // Encode all metrics in the registry in the text format.
/// # let mut buffer = String::new();
/// # encode(&mut buffer, &registry).unwrap();
/// #
/// # let expected = "# HELP my_counter This is my counter.\n".to_owned() +
/// #                "# TYPE my_counter counter\n" +
/// #                "my_counter_total{method=\"GET\"} 1\n" +
/// #                "# EOF\n";
/// # assert_eq!(expected, buffer);
/// ```
// TODO: Consider exposing hash algorithm.
pub struct Family<S, M, C = fn() -> M, H = RandomState> {
    metrics: Arc<RwLock<HashMap<S, M, H>>>,
    /// Function that when called constructs a new metric.
    ///
    /// For most metric types this would simply be its [`Default`]
    /// implementation set through [`Family::default`]. For metric types that
    /// need custom construction logic like
    /// [`Histogram`](crate::metrics::histogram::Histogram) in order to set
    /// specific buckets, a custom constructor is set via
    /// [`Family::new_with_constructor`].
    constructor: C,
}

impl<S: std::fmt::Debug, M: std::fmt::Debug, C, H> std::fmt::Debug for Family<S, M, C, H> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Family")
            .field("metrics", &self.metrics)
            .finish()
    }
}

/// A constructor for creating new metrics in a [`Family`] when calling
/// [`Family::get_or_create`]. Such constructor is provided via
/// [`Family::new_with_constructor`].
///
/// This is mostly used when creating histograms using constructors that need to
/// capture variables.
///
/// ```
/// # use prometheus_client::metrics::family::{Family, MetricConstructor};
/// # use prometheus_client::metrics::histogram::Histogram;
/// struct CustomBuilder {
///     buckets: Vec<f64>,
/// }
///
/// impl MetricConstructor<Histogram> for CustomBuilder {
///     fn new_metric(&self) -> Histogram {
///         // When a new histogram is created, this function will be called.
///         Histogram::new(self.buckets.iter().cloned())
///     }
/// }
///
/// let custom_builder = CustomBuilder { buckets: vec![0.0, 10.0, 100.0] };
/// let metric = Family::<(), Histogram, CustomBuilder>::new_with_constructor(custom_builder);
/// ```
pub trait MetricConstructor<M> {
    /// Create a new instance of the metric type.
    fn new_metric(&self) -> M;
}

/// In cases in which the explicit type of the metric is not required, it is
/// posible to directly provide a closure even if it captures variables.
///
/// ```
/// # use prometheus_client::metrics::family::{Family};
/// # use prometheus_client::metrics::histogram::Histogram;
/// let custom_buckets = [0.0, 10.0, 100.0];
/// let metric = Family::<(), Histogram, _>::new_with_constructor(|| {
///     Histogram::new(custom_buckets.into_iter())
/// });
/// # metric.get_or_create(&());
/// ```
impl<M, F: Fn() -> M> MetricConstructor<M> for F {
    fn new_metric(&self) -> M {
        self()
    }
}

impl<S: Clone + std::hash::Hash + Eq, M: Default, H: Default> Default
    for Family<S, M, fn() -> M, H>
{
    fn default() -> Self {
        Self {
            metrics: Arc::new(RwLock::new(Default::default())),
            constructor: M::default,
        }
    }
}

impl<S: Clone + std::hash::Hash + Eq, M, C, H: Default> Family<S, M, C, H> {
    /// Create a metric family using a custom constructor to construct new
    /// metrics.
    ///
    /// When calling [`Family::get_or_create`] a [`Family`] needs to be able to
    /// construct a new metric in case none exists for the given label set. In
    /// most cases, e.g. for [`Counter`](crate::metrics::counter::Counter)
    /// [`Family`] can just use the [`Default::default`] implementation for the
    /// metric type. For metric types such as
    /// [`Histogram`](crate::metrics::histogram::Histogram) one might want
    /// [`Family`] to construct a
    /// [`Histogram`](crate::metrics::histogram::Histogram) with custom buckets
    /// (see example below). For such case one can use this method. For more
    /// involved constructors see [`MetricConstructor`].
    ///
    /// ```
    /// # use prometheus_client::metrics::family::Family;
    /// # use prometheus_client::metrics::histogram::{exponential_buckets, Histogram};
    /// Family::<Vec<(String, String)>, Histogram>::new_with_constructor(|| {
    ///     Histogram::new(exponential_buckets(1.0, 2.0, 10))
    /// });
    /// ```
    pub fn new_with_constructor(constructor: C) -> Self {
        Self {
            metrics: Arc::new(RwLock::new(HashMap::<S, M, H>::default())),
            constructor,
        }
    }
}

impl<S: Clone + std::hash::Hash + Eq, M: Default, H> Family<S, M, fn() -> M, H> {
    /// Create a metric family using a custom hasher for the hashmap of metrics.
    pub fn new_with_hasher(hasher: H) -> Self {
        Self {
            metrics: Arc::new(RwLock::new(HashMap::with_hasher(hasher))),
            constructor: M::default,
        }
    }
}

impl<S: Clone + std::hash::Hash + Eq, M, C, H> Family<S, M, C, H> {
    /// Create a metric family using a custom constructor to construct new
    /// metrics and a custom hasher for the hashmap of metrics.
    pub fn new_with_constructor_and_hasher(constructor: C, hasher: H) -> Self {
        Self {
            metrics: Arc::new(RwLock::new(HashMap::with_hasher(hasher))),
            constructor,
        }
    }
}

impl<S: Clone + std::hash::Hash + Eq, M, C: MetricConstructor<M>, H: BuildHasher>
    Family<S, M, C, H>
{
    /// Access a metric with the given label set, creating it if one does not
    /// yet exist.
    ///
    /// ```
    /// # use prometheus_client::metrics::counter::{Atomic, Counter};
    /// # use prometheus_client::metrics::family::Family;
    /// #
    /// let family = Family::<Vec<(String, String)>, Counter>::default();
    ///
    /// // Will create the metric with label `method="GET"` on first call and
    /// // return a reference.
    /// family.get_or_create(&vec![("method".to_owned(), "GET".to_owned())]).inc();
    ///
    /// // Will return a reference to the existing metric on all subsequent
    /// // calls.
    /// family.get_or_create(&vec![("method".to_owned(), "GET".to_owned())]).inc();
    /// ```
    pub fn get_or_create(&self, label_set: &S) -> MappedRwLockReadGuard<M> {
        if let Ok(metric) =
            RwLockReadGuard::try_map(self.metrics.read(), |metrics| metrics.get(label_set))
        {
            return metric;
        }

        let mut write_guard = self.metrics.write();

        write_guard
            .entry(label_set.clone())
            .or_insert_with(|| self.constructor.new_metric());

        let read_guard = RwLockWriteGuard::downgrade(write_guard);

        RwLockReadGuard::map(read_guard, |metrics| {
            metrics
                .get(label_set)
                .expect("Metric to exist after creating it.")
        })
    }

    /// Remove a label set from the metric family.
    ///
    /// Returns a bool indicating if a label set was removed or not.
    ///
    /// ```
    /// # use prometheus_client::metrics::counter::{Atomic, Counter};
    /// # use prometheus_client::metrics::family::Family;
    /// #
    /// let family = Family::<Vec<(String, String)>, Counter>::default();
    ///
    /// // Will create the metric with label `method="GET"` on first call and
    /// // return a reference.
    /// family.get_or_create(&vec![("method".to_owned(), "GET".to_owned())]).inc();
    ///
    /// // Will return `true`, indicating that the `method="GET"` label set was
    /// // removed.
    /// assert!(family.remove(&vec![("method".to_owned(), "GET".to_owned())]));
    /// ```
    pub fn remove(&self, label_set: &S) -> bool {
        self.metrics.write().remove(label_set).is_some()
    }

    /// Clear all label sets from the metric family.
    ///
    /// ```
    /// # use prometheus_client::metrics::counter::{Atomic, Counter};
    /// # use prometheus_client::metrics::family::Family;
    /// #
    /// let family = Family::<Vec<(String, String)>, Counter>::default();
    ///
    /// // Will create the metric with label `method="GET"` on first call and
    /// // return a reference.
    /// family.get_or_create(&vec![("method".to_owned(), "GET".to_owned())]).inc();
    ///
    /// // Clear the family of all label sets.
    /// family.clear();
    /// ```
    pub fn clear(&self) {
        self.metrics.write().clear()
    }

    pub(crate) fn read(&self) -> RwLockReadGuard<HashMap<S, M, H>> {
        self.metrics.read()
    }
}

impl<S, M, C: Clone, H: Clone> Clone for Family<S, M, C, H> {
    fn clone(&self) -> Self {
        Family {
            metrics: self.metrics.clone(),
            constructor: self.constructor.clone(),
        }
    }
}

impl<S, M: TypedMetric, C> TypedMetric for Family<S, M, C> {
    const TYPE: MetricType = <M as TypedMetric>::TYPE;
}

impl<S, M, C> EncodeMetric for Family<S, M, C>
where
    S: Clone + std::hash::Hash + Eq + EncodeLabelSet,
    M: EncodeMetric + TypedMetric,
    C: MetricConstructor<M>,
{
    fn encode(&self, mut encoder: MetricEncoder) -> Result<(), std::fmt::Error> {
        let guard = self.read();
        for (label_set, m) in guard.iter() {
            let encoder = encoder.encode_family(label_set)?;
            m.encode(encoder)?;
        }
        Ok(())
    }

    fn metric_type(&self) -> MetricType {
        M::TYPE
    }
}

#[cfg(test)]
mod tests {
    use std::{fmt::Debug, hash::Hasher};

    use super::*;
    use crate::metrics::counter::Counter;
    use crate::metrics::histogram::{exponential_buckets, Histogram};

    #[test]
    fn counter_family() {
        let family = Family::<Vec<(String, String)>, Counter>::default();

        family
            .get_or_create(&vec![("method".to_string(), "GET".to_string())])
            .inc();

        assert_eq!(
            1,
            family
                .get_or_create(&vec![("method".to_string(), "GET".to_string())])
                .get()
        );
    }

    #[test]
    fn histogram_family() {
        Family::<(), Histogram>::new_with_constructor(|| {
            Histogram::new(exponential_buckets(1.0, 2.0, 10))
        });
    }

    #[test]
    fn histogram_family_with_struct_constructor() {
        struct CustomBuilder {
            custom_start: f64,
        }
        impl MetricConstructor<Histogram> for CustomBuilder {
            fn new_metric(&self) -> Histogram {
                Histogram::new(exponential_buckets(self.custom_start, 2.0, 10))
            }
        }

        let custom_builder = CustomBuilder { custom_start: 1.0 };
        Family::<(), Histogram, CustomBuilder>::new_with_constructor(custom_builder);
    }

    #[test]
    fn counter_family_remove() {
        let family = Family::<Vec<(String, String)>, Counter>::default();

        family
            .get_or_create(&vec![("method".to_string(), "GET".to_string())])
            .inc();

        assert_eq!(
            1,
            family
                .get_or_create(&vec![("method".to_string(), "GET".to_string())])
                .get()
        );

        family
            .get_or_create(&vec![("method".to_string(), "POST".to_string())])
            .inc_by(2);

        assert_eq!(
            2,
            family
                .get_or_create(&vec![("method".to_string(), "POST".to_string())])
                .get()
        );

        // Attempt to remove it twice, showing it really was removed on the
        // first attempt.
        assert!(family.remove(&vec![("method".to_string(), "POST".to_string())]));
        assert!(!family.remove(&vec![("method".to_string(), "POST".to_string())]));

        // This should make a new POST label.
        family
            .get_or_create(&vec![("method".to_string(), "POST".to_string())])
            .inc();

        assert_eq!(
            1,
            family
                .get_or_create(&vec![("method".to_string(), "POST".to_string())])
                .get()
        );

        // GET label should have be untouched.
        assert_eq!(
            1,
            family
                .get_or_create(&vec![("method".to_string(), "GET".to_string())])
                .get()
        );
    }

    #[test]
    fn counter_family_clear() {
        let family = Family::<Vec<(String, String)>, Counter>::default();

        // Create a label and check it.
        family
            .get_or_create(&vec![("method".to_string(), "GET".to_string())])
            .inc();

        assert_eq!(
            1,
            family
                .get_or_create(&vec![("method".to_string(), "GET".to_string())])
                .get()
        );

        // Clear it, then try recreating and checking it again.
        family.clear();

        family
            .get_or_create(&vec![("method".to_string(), "GET".to_string())])
            .inc();

        assert_eq!(
            1,
            family
                .get_or_create(&vec![("method".to_string(), "GET".to_string())])
                .get()
        );
    }

    #[derive(Clone, Default)]
    struct DummyHasher;
    impl Hasher for DummyHasher {
        fn finish(&self) -> u64 {
            0
        }

        fn write(&mut self, _bytes: &[u8]) {}
    }
    impl BuildHasher for DummyHasher {
        type Hasher = Self;

        fn build_hasher(&self) -> Self::Hasher {
            Self
        }
    }

    #[test]
    fn family_with_custom_hasher() {
        fn run_family_test<M: Debug>(
            f: Family<&str, M, impl Fn() -> M, impl BuildHasher>,
            record_metric: impl Fn(&M),
        ) {
            eprintln!("checking family {f:?}");
            let m = f.get_or_create(&"a");
            record_metric(&*m);
        }

        let family = Family::<&str, Counter, _, DummyHasher>::default();
        run_family_test(family, |counter: &Counter| {
            counter.inc();
        });

        let family = Family::<&str, Histogram, _, DummyHasher>::new_with_constructor(|| {
            Histogram::new(exponential_buckets(1.0, 2.0, 3))
        });
        run_family_test(family, |histogram: &Histogram| histogram.observe(1.5));

        let family = Family::<&str, Histogram, _, _>::new_with_constructor_and_hasher(
            || Histogram::new(exponential_buckets(1.0, 2.0, 3)),
            DummyHasher,
        );
        run_family_test(family, |histogram: &Histogram| histogram.observe(1.5));
    }
}
