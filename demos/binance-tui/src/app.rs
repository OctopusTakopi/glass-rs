//! Book synchronisation (Binance's documented diff-depth procedure) and the
//! side-by-side application of every update to both books.

use crate::book::{BTreeBook, GlassBook, Level, OrderBook, Side, cross_check};
use crate::feed::{self, DepthEvent, Feed, SymbolSpec};
use crate::stats::Latency;
use std::collections::VecDeque;
use std::sync::mpsc::{Receiver, channel};
use std::time::{Duration, Instant};

/// Full O(book) cross-check every this many events (the O(1) check runs on
/// every event).
const FULL_CHECK_EVERY: u64 = 16;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Phase {
    /// Snapshot applied with this `lastUpdateId`; waiting for the event that
    /// straddles it.
    AwaitFirst(u64),
    /// Applied up to this final update id.
    Live(u64),
}

#[derive(Default)]
pub struct Impl {
    pub apply: Latency,
    pub estimate: Latency,
    /// Last market estimates: (buy cost, lots, sell proceeds, lots).
    pub last_market: Option<((u64, u64), (u64, u64))>,
}

pub struct App {
    pub symbol: String,
    pub spec: SymbolSpec,
    pub btree: BTreeBook,
    pub glass: GlassBook,
    pub btree_stats: Impl,
    pub glass_stats: Impl,
    /// Feed thread -> book thread queueing delay.
    pub queue: Latency,
    pub events: u64,
    pub level_updates: u64,
    pub resyncs: u64,
    pub checks: u64,
    pub full_checks: u64,
    pub check_failures: u64,
    pub first_failure: Option<String>,
    pub crossed: u64,
    pub status: String,
    pub market_lots: u64,
    pub started: Instant,
    phase: Option<Phase>,
    pending: VecDeque<DepthEvent>,
    rx: Receiver<Feed>,
    /// Optional trace-mcp FIFO trigger: fired once, on the first glass apply
    /// slower than `GLASS_SLOW_NS` (set `TRACE_MCP_TRIGGER` to enable).
    trigger: Option<(String, u64)>,
}

impl App {
    pub fn new(symbol: String, market_lots: u64) -> Result<App, String> {
        let spec = feed::symbol_spec(&symbol)?;
        let rx = spawn_stream(&symbol, spec);
        Ok(App {
            symbol,
            spec,
            btree: BTreeBook::default(),
            glass: GlassBook::default(),
            btree_stats: Impl::default(),
            glass_stats: Impl::default(),
            queue: Latency::default(),
            events: 0,
            level_updates: 0,
            resyncs: 0,
            checks: 0,
            full_checks: 0,
            check_failures: 0,
            first_failure: None,
            crossed: 0,
            status: "connecting".into(),
            market_lots,
            started: Instant::now(),
            phase: None,
            pending: VecDeque::new(),
            rx,
            trigger: std::env::var("TRACE_MCP_TRIGGER").ok().map(|p| {
                let ns = std::env::var("GLASS_SLOW_NS")
                    .ok()
                    .and_then(|v| v.parse().ok())
                    .unwrap_or(15_000);
                (p, ns)
            }),
        })
    }

    pub fn live(&self) -> bool {
        matches!(self.phase, Some(Phase::Live(_)))
    }

    /// Drains the feed for at most `budget`. Blocks for the snapshot while
    /// (re)synchronising.
    pub fn pump(&mut self, budget: Duration) -> Result<(), String> {
        let deadline = Instant::now() + budget;
        loop {
            if self.phase.is_none() {
                self.resync()?;
            }
            let ev = match self.pending.pop_front() {
                Some(ev) => ev,
                None => match self.rx.try_recv() {
                    Ok(Feed::Event(ev)) => ev,
                    Ok(Feed::Down(why)) => {
                        self.status = format!("stream down ({why}); reconnecting");
                        std::thread::sleep(Duration::from_secs(1));
                        self.rx = spawn_stream(&self.symbol, self.spec);
                        self.phase = None;
                        continue;
                    }
                    Err(_) => return Ok(()),
                },
            };
            self.handle(ev);
            if Instant::now() >= deadline {
                return Ok(());
            }
        }
    }

    fn resync(&mut self) -> Result<(), String> {
        self.status = "syncing: waiting for the stream".into();
        // Binance: open the stream, buffer it, *then* take the snapshot.
        if self.pending.is_empty() {
            match self.rx.recv_timeout(Duration::from_secs(10)) {
                Ok(Feed::Event(ev)) => self.pending.push_back(ev),
                Ok(Feed::Down(why)) => return Err(format!("stream down: {why}")),
                Err(_) => return Err("no depth events within 10 s".into()),
            }
        }
        self.status = "syncing: fetching snapshot".into();
        let snap = feed::snapshot(&self.symbol, self.spec)?;
        self.btree.clear();
        self.glass.clear();
        for (side, levels) in [(Side::Bid, &snap.bids), (Side::Ask, &snap.asks)] {
            for &l in levels.iter() {
                self.btree.set(side, l);
                self.glass.set(side, l);
            }
        }
        self.phase = Some(Phase::AwaitFirst(snap.last_update_id));
        self.status = format!("snapshot {} applied", snap.last_update_id);
        Ok(())
    }

    fn handle(&mut self, ev: DepthEvent) {
        match self.phase {
            None => self.pending.push_back(ev),
            Some(Phase::AwaitFirst(snap_id)) => {
                if ev.last_id < snap_id {
                    return; // older than the snapshot
                }
                if ev.first_id > snap_id {
                    // The stream is past the snapshot: take a newer one.
                    self.pending.push_front(ev);
                    self.resyncs += 1;
                    self.phase = None;
                    return;
                }
                self.apply(&ev);
                self.phase = Some(Phase::Live(ev.last_id));
                self.status = "live".into();
            }
            Some(Phase::Live(prev)) => {
                if ev.prev_last_id != prev {
                    self.status = format!("gap: pu {} != {prev}; resyncing", ev.prev_last_id);
                    self.pending.push_front(ev);
                    self.resyncs += 1;
                    self.phase = None;
                    return;
                }
                self.apply(&ev);
                self.phase = Some(Phase::Live(ev.last_id));
            }
        }
    }

    fn apply(&mut self, ev: &DepthEvent) {
        self.queue.record(ev.received.elapsed().as_nanos() as u64);
        // Alternate which book goes first, so neither always gets the warm
        // cache for the event's data.
        let glass_ns = if self.events.is_multiple_of(2) {
            let g = time_apply(&mut self.glass, &mut self.glass_stats, ev);
            time_apply(&mut self.btree, &mut self.btree_stats, ev);
            g
        } else {
            time_apply(&mut self.btree, &mut self.btree_stats, ev);
            time_apply(&mut self.glass, &mut self.glass_stats, ev)
        };
        if let Some((path, slow)) = &self.trigger
            && glass_ns > *slow
            && self.events > 20
        {
            eprintln!(
                "trigger: glass apply {glass_ns} ns for update {} ({} bids, {} asks)",
                ev.last_id,
                ev.bids.len(),
                ev.asks.len()
            );
            let _ = std::fs::write(path, b"slow\n");
            self.trigger = None;
        }
        self.events += 1;
        self.level_updates += (ev.bids.len() + ev.asks.len()) as u64;

        if let (Some(b), Some(a)) = (self.glass.best(Side::Bid), self.glass.best(Side::Ask))
            && b.ticks >= a.ticks
        {
            self.crossed += 1;
        }
        let full = self.events.is_multiple_of(FULL_CHECK_EVERY);
        self.checks += 1;
        self.full_checks += full as u64;
        if let Err(e) = cross_check(&self.glass, &self.btree, full) {
            self.check_failures += 1;
            self.first_failure
                .get_or_insert(format!("after update {}: {e}", ev.last_id));
        }
    }

    /// Market-order estimates for `market_lots` on both books, timed.
    pub fn estimate(&mut self) {
        let lots = self.market_lots;
        fn run<B: OrderBook>(book: &B, stats: &mut Impl, lots: u64) {
            let t = Instant::now();
            let buy = std::hint::black_box(book.market(Side::Ask, lots));
            let sell = std::hint::black_box(book.market(Side::Bid, lots));
            stats.estimate.record(t.elapsed().as_nanos() as u64);
            stats.last_market = Some((buy, sell));
        }
        run(&self.btree, &mut self.btree_stats, lots);
        run(&self.glass, &mut self.glass_stats, lots);
    }

    pub fn glass_levels(&self) -> (usize, usize) {
        self.glass.levels()
    }

    pub fn spread(&self) -> Option<(Level, Level)> {
        Some((self.glass.best(Side::Bid)?, self.glass.best(Side::Ask)?))
    }
}

#[inline(never)]
fn time_apply<B: OrderBook>(book: &mut B, stats: &mut Impl, ev: &DepthEvent) -> u64 {
    let t = Instant::now();
    for &l in &ev.bids {
        book.set(Side::Bid, l);
    }
    for &l in &ev.asks {
        book.set(Side::Ask, l);
    }
    let ns = t.elapsed().as_nanos() as u64;
    stats.apply.record(ns);
    ns
}

fn spawn_stream(symbol: &str, spec: SymbolSpec) -> Receiver<Feed> {
    let (tx, rx) = channel();
    let symbol = symbol.to_string();
    std::thread::Builder::new()
        .name("depth-stream".into())
        .spawn(move || feed::stream(&symbol, spec, tx))
        .expect("spawn stream thread");
    rx
}
