use prometheus_client::encoding::EncodeLabelSet;
use prometheus_client::encoding::EncodeLabelValue;

use tide::{Middleware, Next, Request, Result};

#[async_std::main]
async fn main() -> std::result::Result<(), std::io::Error> {
    tide::log::start();

    // let mut registry = Registry::default();
    // let http_requests_total = Family::<Labels, Counter>::default();
    // registry.register(
    //     "http_requests_total",
    //     "Number of HTTP requests",
    //     http_requests_total.clone(),
    // );

    let middleware = MetricsMiddleware {
        // http_requests_total,
    };
    let mut app = tide::with_state(State {
        // registry: Arc::new(registry),
    });

    app.with(middleware);
    app.at("/").get(|_| async { Ok("Hello, world!") });
    app.at("/metrics")
        .get(|_req: tide::Request<State>| async move {
            let encoded = String::new();
            // encode(&mut encoded, &req.state().registry).unwrap();
            let response = tide::Response::builder(200)
                .body(encoded)
                .content_type("application/openmetrics-text; version=1.0.0; charset=utf-8")
                .build();
            Ok(response)
        });
    app.listen("127.0.0.1:8080").await?;

    Ok(())
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, EncodeLabelSet)]
struct Labels {
    method: Method,
    path: String,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq, EncodeLabelValue)]
enum Method {
    Get,
    Put,
}

#[derive(Clone)]
struct State {
    // registry: Arc<Registry>,
}

#[derive(Default)]
struct MetricsMiddleware {
    // http_requests_total: Family<Labels, Counter>,
}

#[tide::utils::async_trait]
impl Middleware<State> for MetricsMiddleware {
    async fn handle(&self, req: Request<State>, next: Next<'_, State>) -> Result {
        let _method = match req.method() {
            http_types::Method::Get => Method::Get,
            http_types::Method::Put => Method::Put,
            _ => todo!(),
        };
        let _path = req.url().path().to_string();
        // let _count = self
        //     .http_requests_total
        //     .get_or_create(&Labels { method, path })
        //     .inc();

        let res = next.run(req).await;
        Ok(res)
    }
}
