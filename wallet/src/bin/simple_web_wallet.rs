//! Simple Rust Web Wallet Server
//! Serves the wallet UI with real blockchain integration

use serde::{Deserialize, Serialize};
use warp::Filter;
use std::sync::Arc;

const WALLET_HTML: &str = include_str!("../../wallet-ui-simple.html");

#[derive(Serialize)]
struct HealthResponse {
    status: String,
}

#[tokio::main]
async fn main() {
    env_logger::init();

    println!("🦀 Starting Rust Wallet Web Server on port 8080");
    println!("📡 Blockchain endpoint: ws://127.0.0.1:9944");
    println!("🌐 Wallet UI: http://localhost:8080/");

    // Serve the wallet HTML
    let index = warp::path::end()
        .map(|| warp::reply::html(WALLET_HTML));

    let wallet_ui = warp::path("wallet-ui.html")
        .map(|| warp::reply::html(WALLET_HTML));

    // Health check endpoint
    let health = warp::path("health")
        .map(|| warp::reply::json(&HealthResponse {
            status: "healthy".to_string(),
        }));

    // Combine routes with CORS for development
    let routes = index
        .or(wallet_ui)
        .or(health)
        .with(warp::cors().allow_any_origin());

    println!("✅ Server ready!");

    warp::serve(routes)
        .run(([0, 0, 0, 0], 8080))
        .await;
}
