//! Binance USDT-M futures market data: REST (symbol filters, depth snapshot)
//! and the `<symbol>@depth@100ms` diff stream on its own thread.

use crate::book::Level;
use crate::fixed::Unit;
use serde::Deserialize;
use std::sync::mpsc::Sender;
use std::time::Instant;

const REST: &str = "https://fapi.binance.com";
const WS: &str = "wss://fstream.binance.com/ws";

#[derive(Clone, Copy, Debug)]
pub struct SymbolSpec {
    pub tick: Unit,
    pub step: Unit,
}

/// Tick size and lot step of a USDT-M perpetual.
pub fn symbol_spec(symbol: &str) -> Result<SymbolSpec, String> {
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
    let body = get(&format!("{REST}/fapi/v1/exchangeInfo"))?;
    let info: Info = serde_json::from_str(&body).map_err(|e| format!("exchangeInfo: {e}"))?;
    let sym = info
        .symbols
        .into_iter()
        .find(|s| s.symbol == symbol)
        .ok_or_else(|| format!("unknown symbol {symbol}"))?;
    if sym.contract_type != "PERPETUAL" {
        return Err(format!(
            "{symbol} is {}, not a perpetual",
            sym.contract_type
        ));
    }
    let filter = |kind: &str, field: &str| -> Result<Unit, String> {
        sym.filters
            .iter()
            .find(|f| f["filterType"] == kind)
            .and_then(|f| f[field].as_str())
            .and_then(Unit::parse)
            .ok_or_else(|| format!("{symbol}: missing {kind}.{field}"))
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

pub fn snapshot(symbol: &str, spec: SymbolSpec) -> Result<Snapshot, String> {
    #[derive(Deserialize)]
    struct Raw<'a> {
        #[serde(rename = "lastUpdateId")]
        last_update_id: u64,
        #[serde(borrow)]
        bids: Vec<[&'a str; 2]>,
        #[serde(borrow)]
        asks: Vec<[&'a str; 2]>,
    }
    let body = get(&format!("{REST}/fapi/v1/depth?symbol={symbol}&limit=1000"))?;
    let raw: Raw = serde_json::from_str(&body).map_err(|e| format!("depth snapshot: {e}"))?;
    Ok(Snapshot {
        last_update_id: raw.last_update_id,
        bids: levels(&raw.bids, spec)?,
        asks: levels(&raw.asks, spec)?,
    })
}

/// One diff-depth event (`depthUpdate`).
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

/// Runs the diff stream until it fails or the receiver is gone.
pub fn stream(symbol: &str, spec: SymbolSpec, tx: Sender<Feed>) {
    let url = format!("{WS}/{}@depth@100ms", symbol.to_ascii_lowercase());
    let err = match tungstenite::connect(&url) {
        Err(e) => format!("connect {url}: {e}"),
        Ok((mut ws, _)) => loop {
            let msg = match ws.read() {
                Ok(m) => m,
                Err(e) => break format!("read: {e}"),
            };
            let received = Instant::now();
            // Pings are answered by tungstenite; flushing sends the pong now.
            let _ = ws.flush();
            let text = match msg {
                tungstenite::Message::Text(t) => t,
                tungstenite::Message::Close(f) => break format!("closed by server: {f:?}"),
                _ => continue,
            };
            match parse_event(text.as_str(), spec, received) {
                Ok(ev) => {
                    if tx.send(Feed::Event(ev)).is_err() {
                        return;
                    }
                }
                Err(e) => break format!("bad event: {e}"),
            }
        },
    };
    let _ = tx.send(Feed::Down(err));
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

fn get(url: &str) -> Result<String, String> {
    ureq::get(url)
        .call()
        .map_err(|e| format!("GET {url}: {e}"))?
        .into_string()
        .map_err(|e| format!("GET {url}: {e}"))
}
