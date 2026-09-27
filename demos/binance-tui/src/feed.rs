//! Binance USDT-M futures market data: REST (symbol filters, depth snapshot)
//! and the `<symbol>@depth@100ms` diff stream on its own thread.
//!
//! Every network operation is bounded in time, so a dead peer or a half-open
//! connection surfaces as an error the caller recovers from, never a hang.
//!
//! Test hooks (environment): `BINANCE_TUI_REST` / `BINANCE_TUI_WS` override
//! the endpoints, `BINANCE_TUI_CHAOS_SECS=N` drops each stream connection
//! after N seconds to exercise reconnection, and `BINANCE_TUI_AUDIT_SECS=N`
//! (read by the app) audits against the exchange every N seconds.

use crate::book::Level;
use crate::fixed::Unit;
use serde::Deserialize;
use std::fmt;
use std::net::{Shutdown, TcpStream, ToSocketAddrs};
use std::sync::OnceLock;
use std::sync::mpsc::Sender;
use std::time::{Duration, Instant};
use tungstenite::client::IntoClientRequest;

const REST: &str = "https://fapi.binance.com";
const WS: &str = "wss://fstream.binance.com/ws";

/// TCP connect, TLS + WebSocket handshake, and socket writes.
const CONNECT_TIMEOUT: Duration = Duration::from_secs(10);
/// A whole REST request.
const HTTP_TIMEOUT: Duration = Duration::from_secs(30);
/// No depth data for this long means the connection is dead or stalled.
/// BTCUSDT sends a frame every 100 ms; Binance pings every 3 minutes, so
/// pings alone do not keep a connection alive.
pub const STALE_AFTER: Duration = Duration::from_secs(60);

fn endpoint(var: &str, default: &str) -> String {
    std::env::var(var).unwrap_or_else(|_| default.to_string())
}

/// A failed REST call.
#[derive(Debug)]
pub struct FetchError {
    pub msg: String,
    /// How long the server asked us to back off (HTTP 429 / 418).
    pub retry_after: Option<Duration>,
    /// Retrying cannot help (unknown symbol, not a perpetual).
    pub fatal: bool,
}

impl FetchError {
    fn transient(msg: String) -> FetchError {
        FetchError {
            msg,
            retry_after: None,
            fatal: false,
        }
    }

    fn fatal(msg: String) -> FetchError {
        FetchError {
            msg,
            retry_after: None,
            fatal: true,
        }
    }
}

impl fmt::Display for FetchError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(&self.msg)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct SymbolSpec {
    pub tick: Unit,
    pub step: Unit,
}

/// Tick size and lot step of a USDT-M perpetual.
pub fn symbol_spec(symbol: &str) -> Result<SymbolSpec, FetchError> {
    #[derive(Deserialize)]
    struct Info {
        symbols: Vec<Sym>,
    }
    #[derive(Deserialize)]
    struct Sym {
        symbol: String,
        #[serde(rename = "contractType")]
        contract_type: String,
        filters: Vec<serde_json::Value>,
    }
    let rest = endpoint("BINANCE_TUI_REST", REST);
    let body = get(&format!("{rest}/fapi/v1/exchangeInfo"))?;
    let info: Info = serde_json::from_str(&body)
        .map_err(|e| FetchError::transient(format!("exchangeInfo: {e}")))?;
    let sym = info
        .symbols
        .into_iter()
        .find(|s| s.symbol == symbol)
        .ok_or_else(|| FetchError::fatal(format!("unknown symbol {symbol}")))?;
    if sym.contract_type != "PERPETUAL" {
        return Err(FetchError::fatal(format!(
            "{symbol} is {}, not a perpetual",
            sym.contract_type
        )));
    }
    let filter = |kind: &str, field: &str| -> Result<Unit, FetchError> {
        sym.filters
            .iter()
            .find(|f| f["filterType"] == kind)
            .and_then(|f| f[field].as_str())
            .and_then(Unit::parse)
            .ok_or_else(|| FetchError::fatal(format!("{symbol}: missing {kind}.{field}")))
    };
    Ok(SymbolSpec {
        tick: filter("PRICE_FILTER", "tickSize")?,
        step: filter("LOT_SIZE", "stepSize")?,
    })
}

/// A REST depth snapshot, converted to ticks/lots.
pub struct Snapshot {
    pub last_update_id: u64,
    pub bids: Vec<Level>,
    pub asks: Vec<Level>,
}

pub fn snapshot(symbol: &str, spec: SymbolSpec) -> Result<Snapshot, FetchError> {
    #[derive(Deserialize)]
    struct Raw<'a> {
        #[serde(rename = "lastUpdateId")]
        last_update_id: u64,
        #[serde(borrow)]
        bids: Vec<[&'a str; 2]>,
        #[serde(borrow)]
        asks: Vec<[&'a str; 2]>,
    }
    let rest = endpoint("BINANCE_TUI_REST", REST);
    let body = get(&format!("{rest}/fapi/v1/depth?symbol={symbol}&limit=1000"))?;
    let bad = |e: String| FetchError::transient(format!("depth snapshot: {e}"));
    let raw: Raw = serde_json::from_str(&body).map_err(|e| bad(e.to_string()))?;
    Ok(Snapshot {
        last_update_id: raw.last_update_id,
        bids: levels(&raw.bids, spec).map_err(bad)?,
        asks: levels(&raw.asks, spec).map_err(bad)?,
    })
}

/// One diff-depth event (`depthUpdate`).
#[derive(Clone)]
pub struct DepthEvent {
    /// `U`: first update id in the event.
    pub first_id: u64,
    /// `u`: final update id in the event.
    pub last_id: u64,
    /// `pu`: final update id of the previous event.
    pub prev_last_id: u64,
    pub bids: Vec<Level>,
    pub asks: Vec<Level>,
    /// When the frame arrived on the feed thread.
    pub received: Instant,
}

pub enum Feed {
    Event(DepthEvent),
    /// The stream failed; the main thread reconnects and resyncs.
    Down(String),
}

/// Runs the diff stream until it fails (then reports why) or the receiver
/// is gone (then exits quietly).
pub fn stream(symbol: &str, spec: SymbolSpec, tx: Sender<Feed>) {
    if let Err(why) = run_stream(symbol, spec, &tx) {
        let _ = tx.send(Feed::Down(why));
    }
}

fn run_stream(symbol: &str, spec: SymbolSpec, tx: &Sender<Feed>) -> Result<(), String> {
    let ws_base = endpoint("BINANCE_TUI_WS", WS);
    let url = format!("{ws_base}/{}@depth@100ms", symbol.to_ascii_lowercase());
    let chaos = std::env::var("BINANCE_TUI_CHAOS_SECS")
        .ok()
        .and_then(|v| v.parse().ok())
        .map(Duration::from_secs);
    let (mut ws, sock) = connect(&url)?;
    let opened = Instant::now();
    let mut last_data = opened;
    loop {
        let msg = ws.read().map_err(|e| match e {
            // The socket read timeout: nothing at all arrived for STALE_AFTER.
            tungstenite::Error::Io(io)
                if matches!(
                    io.kind(),
                    std::io::ErrorKind::WouldBlock | std::io::ErrorKind::TimedOut
                ) =>
            {
                format!("no frames for {} s", STALE_AFTER.as_secs())
            }
            e => format!("read: {e}"),
        })?;
        let received = Instant::now();
        // Pings are answered by tungstenite; flushing sends the pong now.
        let _ = ws.flush();
        match msg {
            tungstenite::Message::Text(text) => {
                let ev = parse_event(text.as_str(), spec, received)
                    .map_err(|e| format!("bad event: {e}"))?;
                last_data = received;
                if tx.send(Feed::Event(ev)).is_err() {
                    return Ok(());
                }
            }
            tungstenite::Message::Close(f) => return Err(format!("closed by server: {f:?}")),
            _ => {}
        }
        if received - last_data > STALE_AFTER {
            return Err(format!("no depth data for {} s", STALE_AFTER.as_secs()));
        }
        if let Some(after) = chaos
            && opened.elapsed() >= after
        {
            let _ = sock.shutdown(Shutdown::Both);
            return Err(format!(
                "chaos: dropped the connection after {} s",
                after.as_secs()
            ));
        }
    }
}

type Ws = tungstenite::WebSocket<tungstenite::stream::MaybeTlsStream<TcpStream>>;

/// Opens the WebSocket over a TCP socket we own, so every phase has a
/// deadline: the connect, the TLS and WebSocket handshakes (bounded by
/// `CONNECT_TIMEOUT`), and each later read (bounded by `STALE_AFTER`, which
/// turns a half-open connection into an error). Also returns a handle to the
/// socket.
fn connect(url: &str) -> Result<(Ws, TcpStream), String> {
    let req = url
        .into_client_request()
        .map_err(|e| format!("bad url {url}: {e}"))?;
    let host = req.uri().host().ok_or("url has no host")?.to_string();
    let port = req
        .uri()
        .port_u16()
        .unwrap_or(if req.uri().scheme_str() == Some("ws") {
            80
        } else {
            443
        });
    let addrs = (host.as_str(), port)
        .to_socket_addrs()
        .map_err(|e| format!("resolve {host}: {e}"))?;
    let mut last = format!("resolve {host}: no addresses");
    let tcp = addrs
        .into_iter()
        .find_map(|a| {
            TcpStream::connect_timeout(&a, CONNECT_TIMEOUT)
                .map_err(|e| last = format!("connect {a}: {e}"))
                .ok()
        })
        .ok_or(last)?;
    // Socket options apply to the socket, so this clone controls the one the
    // WebSocket owns.
    let sock = tcp.try_clone().map_err(|e| format!("socket: {e}"))?;
    let opt = |r: std::io::Result<()>| r.map_err(|e| format!("socket: {e}"));
    opt(sock.set_nodelay(true))?;
    opt(sock.set_write_timeout(Some(CONNECT_TIMEOUT)))?;
    opt(sock.set_read_timeout(Some(CONNECT_TIMEOUT)))?;
    let (ws, _) =
        tungstenite::client_tls_with_config(req, tcp, None, None).map_err(|e| match e {
            // The read timeout fired mid-handshake.
            tungstenite::HandshakeError::Interrupted(_) => format!(
                "handshake {url}: no answer within {} s",
                CONNECT_TIMEOUT.as_secs()
            ),
            tungstenite::HandshakeError::Failure(e) => format!("handshake {url}: {e}"),
        })?;
    opt(sock.set_read_timeout(Some(STALE_AFTER)))?;
    Ok((ws, sock))
}

fn parse_event(text: &str, spec: SymbolSpec, received: Instant) -> Result<DepthEvent, String> {
    #[derive(Deserialize)]
    struct Raw<'a> {
        #[serde(rename = "U")]
        first_id: u64,
        #[serde(rename = "u")]
        last_id: u64,
        pu: u64,
        #[serde(borrow)]
        b: Vec<[&'a str; 2]>,
        #[serde(borrow)]
        a: Vec<[&'a str; 2]>,
    }
    let raw: Raw = serde_json::from_str(text).map_err(|e| e.to_string())?;
    Ok(DepthEvent {
        first_id: raw.first_id,
        last_id: raw.last_id,
        prev_last_id: raw.pu,
        bids: levels(&raw.b, spec)?,
        asks: levels(&raw.a, spec)?,
        received,
    })
}

fn levels(raw: &[[&str; 2]], spec: SymbolSpec) -> Result<Vec<Level>, String> {
    raw.iter()
        .map(|[p, q]| {
            let ticks = spec
                .tick
                .to_units(p)
                .ok_or_else(|| format!("price {p} off the tick grid"))?;
            let lots = spec
                .step
                .to_units(q)
                .ok_or_else(|| format!("size {q} off the lot grid"))?;
            // u32::MAX is reserved (it maps a bid to key 0 and back), and no
            // listed contract comes near it.
            let ticks = u32::try_from(ticks)
                .ok()
                .filter(|&t| t < u32::MAX)
                .ok_or("price out of range")?;
            Ok(Level { ticks, lots })
        })
        .collect()
}

fn get(url: &str) -> Result<String, FetchError> {
    static AGENT: OnceLock<ureq::Agent> = OnceLock::new();
    let agent = AGENT.get_or_init(|| {
        ureq::AgentBuilder::new()
            .timeout_connect(CONNECT_TIMEOUT)
            .timeout(HTTP_TIMEOUT)
            .build()
    });
    match agent.get(url).call() {
        Ok(resp) => resp
            .into_string()
            .map_err(|e| FetchError::transient(format!("GET {url}: {e}"))),
        Err(ureq::Error::Status(code, resp)) => {
            // 429: over the request-weight limit; 418: IP banned for
            // ignoring 429s. Both say, in seconds, when to come back.
            let asked = resp
                .header("Retry-After")
                .and_then(|v| v.trim().parse().ok())
                .map(Duration::from_secs);
            let retry_after =
                asked.or((code == 429 || code == 418).then_some(Duration::from_secs(60)));
            Err(FetchError {
                msg: format!("GET {url}: HTTP {code}"),
                retry_after,
                fatal: false,
            })
        }
        Err(e) => Err(FetchError::transient(format!("GET {url}: {e}"))),
    }
}
