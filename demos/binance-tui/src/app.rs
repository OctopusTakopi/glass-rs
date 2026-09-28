//! Book synchronisation (Binance's documented diff-depth procedure), the
//! side-by-side application of every update to both books, and recovery.
//!
//! No network failure is fatal: a dropped or stalled stream reconnects, and a
//! gap or a lagging snapshot resyncs, each after an exponential back-off that
//! resets once the book has been live for a while. A disagreement between the
//! books is recorded (with a dump of the evidence) and followed by a resync,
//! so later checks stay meaningful.

use crate::audit;
use crate::book::{BTreeBook, GlassBook, Level, OrderBook, Side, cross_check, exec_check};
use crate::feed::{self, DepthEvent, Feed, FetchError, Snapshot, SymbolSpec};
use crate::stats::Latency;
use std::collections::{BTreeSet, VecDeque};
use std::fmt::Write as _;
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{Receiver, TryRecvError, channel};
use std::time::{Duration, Instant};

/// Set by SIGINT/SIGTERM; long waits and the headless loop check it.
pub static STOP: AtomicBool = AtomicBool::new(false);

/// Full O(book) cross-check every this many events (the O(1) check runs on
/// every event).
const FULL_CHECK_EVERY: u64 = 16;
/// How often to run the execution check (`book::exec_check`).
const EXEC_CHECK_EVERY: Duration = Duration::from_secs(10);
/// Back-off after the n-th consecutive failure: 1 s, 2 s, 4 s, ... capped.
const MAX_BACKOFF: Duration = Duration::from_secs(300);
/// Live events after which the failure streak is forgiven.
const HEALTHY_AFTER: u64 = 600;
/// Events buffered while resyncing. Dropping older ones is safe: the `U`/`pu`
/// checks catch any gap it opens.
const MAX_PENDING: usize = 20_000;
/// Recent events kept for a mismatch dump.
const HISTORY: usize = 256;
/// Mismatch dumps written per run.
const MAX_DUMPS: u64 = 5;
/// Crossed-book onsets logged per run.
const MAX_CROSS_LOGS: u64 = 20;
/// How often to audit the books against a fresh REST snapshot (see
/// `audit`), and the first audit's delay after start.
const AUDIT_EVERY: Duration = Duration::from_secs(300);
const FIRST_AUDIT: Duration = Duration::from_secs(60);
/// Retry delay when an audit could not be placed (the snapshot was older
/// than the book, a fetch failed, or a resync intervened).
const AUDIT_RETRY: Duration = Duration::from_secs(30);
/// Re-sync once fewer than this many levels on a side remain inside the
/// reach of the snapshot the books were synced from (see `left_reach`).
/// BTC's 1000-level reach spans only ~$100-300 a side, so the margin keeps
/// the new snapshot ahead of a fast move.
const MIN_KNOWN: usize = 300;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Phase {
    /// Needs a snapshot, taken no earlier than `at` and only once the stream
    /// has delivered an event (Binance: buffer the stream, *then* snapshot).
    Resync { at: Instant },
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
    pub reconnects: u64,
    pub snapshots: u64,
    pub checks: u64,
    pub full_checks: u64,
    pub check_failures: u64,
    pub exec_checks: u64,
    pub exec_ops: u64,
    pub exec_failures: u64,
    /// L2 audits against the exchange: completed (and how many of those at
    /// an exact event boundary), not placed, and failed.
    pub audits: u64,
    pub audits_exact: u64,
    /// Price levels the passing audits compared (per book).
    pub audit_levels: u64,
    pub audits_skipped: u64,
    pub audit_failures: u64,
    pub first_failure: Option<String>,
    /// Events after which the book was crossed, and how often it became so.
    pub crossed: u64,
    pub cross_onsets: u64,
    pub status: String,
    pub market_lots: u64,
    pub started: Instant,
    phase: Phase,
    pending: VecDeque<DepthEvent>,
    /// The stream; `None` while waiting to reconnect at `retry_at`.
    conn: Option<Receiver<Feed>>,
    retry_at: Instant,
    /// Consecutive failures (sets the back-off), and live events since the
    /// last one.
    failures: u32,
    healthy: u64,
    was_crossed: bool,
    history: VecDeque<DepthEvent>,
    last_exec: Instant,
    audit: Option<audit::Pending>,
    audit_due: Instant,
    /// What the snapshot the books were synced from vouched for: outside
    /// it, resting orders that have not changed since are unknown.
    synced: audit::Reach,
    /// `AUDIT_EVERY`, or `BINANCE_TUI_AUDIT_SECS` (a test hook).
    audit_every: Duration,
    rng: u64,
    /// Echo status changes to stderr (headless; the TUI shows them instead).
    log: bool,
    /// Where mismatch dumps go.
    dump_dir: Option<PathBuf>,
    dumps: u64,
    /// Optional trace-mcp FIFO trigger: fired once, on the first glass apply
    /// slower than `GLASS_SLOW_NS` (set `TRACE_MCP_TRIGGER` to enable).
    trigger: Option<(String, u64)>,
}

fn backoff_for(failures: u32) -> Duration {
    Duration::from_secs(1 << failures.min(16)).min(MAX_BACKOFF)
}

impl App {
    /// Fetches the symbol's tick/lot grid, retrying transient failures, and
    /// opens the stream.
    pub fn new(
        symbol: String,
        market_lots: u64,
        log: bool,
        dump_dir: Option<PathBuf>,
    ) -> Result<App, String> {
        let mut failures = 0;
        let spec = loop {
            match feed::symbol_spec(&symbol) {
                Ok(spec) => break spec,
                Err(e) if e.fatal => return Err(e.msg),
                Err(e) => {
                    let wait = backoff_for(failures).max(e.retry_after.unwrap_or_default());
                    failures += 1;
                    eprintln!(
                        "exchangeInfo failed ({e}); retrying in {} s",
                        wait.as_secs()
                    );
                    let until = Instant::now() + wait;
                    while Instant::now() < until {
                        if STOP.load(Ordering::Relaxed) {
                            return Err("stopped".into());
                        }
                        std::thread::sleep(Duration::from_millis(100));
                    }
                }
            }
        };
        let mut app = App::offline(symbol, spec, market_lots, log, dump_dir);
        app.open_stream();
        Ok(app)
    }

    /// An app with no stream (tests drive `load_snapshot` and `handle`).
    fn offline(
        symbol: String,
        spec: SymbolSpec,
        market_lots: u64,
        log: bool,
        dump_dir: Option<PathBuf>,
    ) -> App {
        let now = Instant::now();
        let audit_every = std::env::var("BINANCE_TUI_AUDIT_SECS")
            .ok()
            .and_then(|v| v.parse().ok())
            .map_or(AUDIT_EVERY, Duration::from_secs);
        App {
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
            reconnects: 0,
            snapshots: 0,
            checks: 0,
            full_checks: 0,
            check_failures: 0,
            exec_checks: 0,
            exec_ops: 0,
            exec_failures: 0,
            audits: 0,
            audits_exact: 0,
            audit_levels: 0,
            audits_skipped: 0,
            audit_failures: 0,
            first_failure: None,
            crossed: 0,
            cross_onsets: 0,
            status: String::new(),
            market_lots,
            started: now,
            phase: Phase::Resync { at: now },
            pending: VecDeque::new(),
            conn: None,
            retry_at: now,
            failures: 0,
            healthy: 0,
            was_crossed: false,
            history: VecDeque::with_capacity(HISTORY),
            last_exec: now,
            audit: None,
            synced: audit::Reach::default(),
            audit_due: now + FIRST_AUDIT.min(audit_every),
            audit_every,
            rng: 0x9E37_79B9_7F4A_7C15,
            log,
            dump_dir,
            dumps: 0,
            trigger: std::env::var("TRACE_MCP_TRIGGER").ok().map(|p| {
                let ns = std::env::var("GLASS_SLOW_NS")
                    .ok()
                    .and_then(|v| v.parse().ok())
                    .unwrap_or(15_000);
                (p, ns)
            }),
        }
    }

    pub fn live(&self) -> bool {
        matches!(self.phase, Phase::Live(_))
    }

    fn note(&mut self, msg: String) {
        if self.log {
            eprintln!("{msg}");
        }
        self.status = msg;
    }

    /// Registers a failure and returns how long to back off.
    fn backoff(&mut self) -> Duration {
        let wait = backoff_for(self.failures);
        self.failures += 1;
        self.healthy = 0;
        wait
    }

    fn open_stream(&mut self) {
        let (tx, rx) = channel();
        let (symbol, spec) = (self.symbol.clone(), self.spec);
        let spawned = std::thread::Builder::new()
            .name("depth-stream".into())
            .spawn(move || feed::stream(&symbol, spec, tx));
        match spawned {
            Ok(_) => {
                self.conn = Some(rx);
                self.phase = Phase::Resync { at: Instant::now() };
                self.note("connecting".into());
            }
            Err(e) => self.disconnect(&format!("spawn stream thread: {e}"), None),
        }
    }

    /// Drops the stream (its thread exits on its next send or read timeout)
    /// and schedules a reconnect.
    fn disconnect(&mut self, why: &str, retry_after: Option<Duration>) {
        self.drop_audit();
        self.conn = None;
        self.pending.clear();
        let wait = self.backoff().max(retry_after.unwrap_or_default());
        self.retry_at = Instant::now() + wait;
        self.note(format!(
            "stream down ({why}); reconnecting in {} s",
            wait.as_secs()
        ));
    }

    fn reconnect(&mut self) {
        self.reconnects += 1;
        // Binance does change a contract's tick size or lot step, and a stale
        // grid rejects every event; refresh it (weight 1).
        match feed::symbol_spec(&self.symbol) {
            Ok(spec) => self.spec = spec,
            Err(e) => self.note(format!(
                "exchangeInfo failed ({e}); keeping the previous tick grid"
            )),
        }
        self.open_stream();
    }

    /// Drains the feed for at most `budget`. Never fails: every problem ends
    /// in a scheduled reconnect or resync.
    pub fn pump(&mut self, budget: Duration) {
        let deadline = Instant::now() + budget;
        loop {
            let Some(rx) = &self.conn else {
                if Instant::now() < self.retry_at {
                    return;
                }
                self.reconnect();
                continue;
            };
            match rx.try_recv() {
                Ok(Feed::Event(ev)) => {
                    if self.pending.len() >= MAX_PENDING {
                        self.pending.pop_front();
                    }
                    self.pending.push_back(ev);
                }
                Ok(Feed::Down(why)) => {
                    self.disconnect(&why, None);
                    continue;
                }
                Err(TryRecvError::Disconnected) => {
                    self.disconnect("stream thread exited", None);
                    continue;
                }
                Err(TryRecvError::Empty) => {
                    self.drain();
                    return;
                }
            }
            self.drain();
            if Instant::now() >= deadline {
                return;
            }
        }
    }

    /// Applies buffered events, taking a snapshot first when one is due.
    fn drain(&mut self) {
        loop {
            if let Phase::Resync { at } = self.phase {
                if self.pending.is_empty() || Instant::now() < at {
                    return;
                }
                if let Err(e) = self.snapshot() {
                    let wait = self.backoff().max(e.retry_after.unwrap_or_default());
                    self.phase = Phase::Resync {
                        at: Instant::now() + wait,
                    };
                    self.note(format!(
                        "snapshot failed ({e}); retrying in {} s",
                        wait.as_secs()
                    ));
                    return;
                }
            }
            let Some(ev) = self.pending.pop_front() else {
                return;
            };
            self.handle(ev);
        }
    }

    fn snapshot(&mut self) -> Result<(), FetchError> {
        self.note("syncing: fetching snapshot".into());
        let snap = feed::snapshot(&self.symbol, self.spec)?;
        self.load_snapshot(snap);
        Ok(())
    }

    /// Replaces both books with `snap` and waits for the event straddling it.
    fn load_snapshot(&mut self, snap: Snapshot) {
        self.snapshots += 1;
        self.drop_audit();
        self.synced = audit::Reach::of(&snap);
        self.btree.clear();
        self.glass.clear();
        for (side, levels) in [(Side::Bid, &snap.bids), (Side::Ask, &snap.asks)] {
            for &l in levels.iter() {
                self.btree.set(side, l);
                self.glass.set(side, l);
            }
        }
        self.was_crossed = false;
        self.phase = Phase::AwaitFirst(snap.last_update_id);
        self.note(format!(
            "snapshot {} applied ({} bids, {} asks)",
            snap.last_update_id,
            snap.bids.len(),
            snap.asks.len()
        ));
    }

    /// Puts `ev` back and schedules a fresh snapshot.
    fn resync(&mut self, ev: DepthEvent, why: String) {
        self.drop_audit();
        self.pending.push_front(ev);
        self.resyncs += 1;
        let wait = self.backoff();
        self.phase = Phase::Resync {
            at: Instant::now() + wait,
        };
        self.note(format!("{why}; resyncing in {} s", wait.as_secs()));
    }

    fn handle(&mut self, ev: DepthEvent) {
        match self.phase {
            Phase::Resync { .. } => self.pending.push_front(ev),
            Phase::AwaitFirst(snap_id) => {
                if ev.last_id < snap_id {
                    return; // older than the snapshot
                }
                if ev.first_id > snap_id {
                    // The snapshot endpoint lags the stream: take a newer one.
                    self.resync(ev, format!("snapshot {snap_id} older than the stream"));
                    return;
                }
                let id = ev.last_id;
                if self.apply(ev) {
                    self.phase = Phase::Live(id);
                    self.note("live".into());
                }
            }
            Phase::Live(prev) => {
                if ev.prev_last_id != prev {
                    let why = format!("gap: pu {} != {prev}", ev.prev_last_id);
                    self.resync(ev, why);
                    return;
                }
                let (pu, id) = (ev.prev_last_id, ev.last_id);
                let touched = self.audit.as_ref().map(|_| {
                    let prices = |ls: &[Level]| ls.iter().map(|l| l.ticks).collect::<BTreeSet<_>>();
                    (prices(&ev.bids), prices(&ev.asks))
                });
                if self.apply(ev) {
                    self.phase = Phase::Live(id);
                    self.audit_step(pu, id, touched);
                }
            }
        }
    }

    /// After the live event `(pu, u]` is applied: completes a pending audit
    /// the event reached, or starts one when due.
    fn audit_step(&mut self, pu: u64, u: u64, touched: Option<(BTreeSet<u32>, BTreeSet<u32>)>) {
        if let Some(p) = &self.audit {
            let target = p.id;
            if target == u {
                self.finish_audit(&BTreeSet::new(), &BTreeSet::new());
            } else if pu < target && target < u {
                let (bids, asks) = touched.unwrap_or_default();
                self.finish_audit(&bids, &asks);
            } else if target <= pu {
                // Cannot happen (each event is checked); count it, move on.
                self.drop_audit();
            }
            return;
        }
        if Instant::now() < self.audit_due {
            return;
        }
        // Blocks the book thread for one REST round trip; events queue.
        match feed::snapshot(&self.symbol, self.spec) {
            Ok(snap) => self.begin_audit(snap, u),
            Err(e) => {
                self.audits_skipped += 1;
                self.audit_due = Instant::now() + AUDIT_RETRY;
                self.note(format!(
                    "audit snapshot failed ({e}); retrying in {} s",
                    AUDIT_RETRY.as_secs()
                ));
            }
        }
    }

    /// Places an audit against `snap`, the books being at update `u`.
    fn begin_audit(&mut self, snap: Snapshot, u: u64) {
        self.audit_due = Instant::now() + self.audit_every;
        self.audit = Some(audit::Pending::new(&snap));
        match snap.last_update_id.cmp(&u) {
            std::cmp::Ordering::Equal => self.finish_audit(&BTreeSet::new(), &BTreeSet::new()),
            // The REST snapshot is older than the books: nothing to compare.
            std::cmp::Ordering::Less => {
                self.drop_audit();
                self.audit_due = Instant::now() + AUDIT_RETRY;
            }
            std::cmp::Ordering::Greater => {} // completes when the stream gets there
        }
    }

    fn finish_audit(&mut self, exempt_bids: &BTreeSet<u32>, exempt_asks: &BTreeSet<u32>) {
        let Some(p) = self.audit.take() else { return };
        let exact = exempt_bids.is_empty() && exempt_asks.is_empty();
        let (diffs, judged) = audit::diff(
            &self.btree,
            &self.glass,
            self.synced,
            &p,
            exempt_bids,
            exempt_asks,
        );
        if diffs.is_empty() {
            self.audits += 1;
            self.audits_exact += exact as u64;
            self.audit_levels += judged as u64;
            return;
        }
        self.audit_failures += 1;
        let shown = diffs
            .iter()
            .take(12)
            .cloned()
            .collect::<Vec<_>>()
            .join("; ");
        self.fail(format!(
            "AUDIT MISMATCH vs exchange snapshot {} ({} levels differ{}): {shown}",
            p.id,
            diffs.len(),
            if exact {
                ""
            } else {
                ", straddling event's levels exempt"
            }
        ));
    }

    /// Abandons a pending audit (a resync or disconnect made it moot).
    fn drop_audit(&mut self) {
        if self.audit.take().is_some() {
            self.audits_skipped += 1;
            self.audit_due = self.audit_due.min(Instant::now() + AUDIT_RETRY);
        }
    }

    /// Applies `ev` to both books and cross-checks them; `false` (after a
    /// mismatch, which schedules a resync) if they disagree.
    fn apply(&mut self, ev: DepthEvent) -> bool {
        self.queue.record(ev.received.elapsed().as_nanos() as u64);
        // Alternate which book goes first, so neither always gets the warm
        // cache for the event's data.
        let glass_ns = if self.events.is_multiple_of(2) {
            let g = time_apply(&mut self.glass, &mut self.glass_stats, &ev);
            time_apply(&mut self.btree, &mut self.btree_stats, &ev);
            g
        } else {
            time_apply(&mut self.btree, &mut self.btree_stats, &ev);
            time_apply(&mut self.glass, &mut self.glass_stats, &ev)
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
        self.healthy += 1;
        if self.healthy == HEALTHY_AFTER {
            self.failures = 0;
        }

        let crossed = match (self.btree.best(Side::Bid), self.btree.best(Side::Ask)) {
            (Some(b), Some(a)) => b.ticks >= a.ticks,
            _ => false,
        };
        if crossed {
            self.crossed += 1;
            if !self.was_crossed {
                self.cross_onsets += 1;
                if self.log && self.cross_onsets <= MAX_CROSS_LOGS {
                    eprintln!(
                        "note: book crossed after update {} (bid {:?} >= ask {:?}); feed data, both books agree on it",
                        ev.last_id,
                        self.btree.best(Side::Bid),
                        self.btree.best(Side::Ask)
                    );
                }
            }
        }
        self.was_crossed = crossed;

        let id = ev.last_id;
        if self.history.len() == HISTORY {
            self.history.pop_front();
        }
        self.history.push_back(ev);

        let full = self.events.is_multiple_of(FULL_CHECK_EVERY);
        self.checks += 1;
        self.full_checks += full as u64;
        if let Err(e) = cross_check(&self.glass, &self.btree, full) {
            self.check_failures += 1;
            self.fail(format!("MISMATCH after update {id}: {e}"));
            return false;
        }
        if let Some(why) = self.left_reach() {
            // Not a failure: the book is only complete near the price it was
            // synced at, so a long run re-syncs as the market moves. Checked
            // on every update: BTC can cross its whole ~1000-level reach
            // within the 16 updates between full checks.
            self.drop_audit();
            self.resyncs += 1;
            self.phase = Phase::Resync { at: Instant::now() };
            self.note(format!("{why}; resyncing"));
            return false;
        }

        if self.last_exec.elapsed() >= EXEC_CHECK_EVERY {
            self.last_exec = Instant::now();
            self.exec_checks += 1;
            match exec_check(&self.glass, &self.btree, &mut self.rng) {
                Ok(ops) => self.exec_ops += ops,
                Err(e) => {
                    self.exec_failures += 1;
                    self.fail(format!("EXEC MISMATCH at update {id}: {e}"));
                    return false;
                }
            }
        }
        true
    }

    /// Whether the market has moved (nearly) out of the price range the
    /// sync snapshot vouched for, where the top of the book could be missing
    /// resting orders the stream never mentioned.
    fn left_reach(&self) -> Option<String> {
        if let Some(floor) = self.synced.bid_floor {
            let known = self.btree.count_from(Side::Bid, floor, MIN_KNOWN);
            if known < MIN_KNOWN {
                return Some(format!(
                    "only {known} bids left above the synced floor {floor}"
                ));
            }
        }
        if let Some(ceiling) = self.synced.ask_ceiling {
            let known = self.btree.count_from(Side::Ask, ceiling, MIN_KNOWN);
            if known < MIN_KNOWN {
                return Some(format!(
                    "only {known} asks left below the synced ceiling {ceiling}"
                ));
            }
        }
        None
    }

    /// Records a disagreement, dumps the evidence, and resyncs: the books
    /// have diverged, so later checks would only repeat the same failure.
    fn fail(&mut self, msg: String) {
        if self.log {
            eprintln!("{msg}");
        }
        self.first_failure.get_or_insert_with(|| msg.clone());
        self.dump(&msg);
        self.resyncs += 1;
        // Backed off like any resync: a disagreement that recurs must not
        // turn into a stream of snapshot requests.
        let wait = self.backoff();
        self.phase = Phase::Resync {
            at: Instant::now() + wait,
        };
        self.status = msg;
    }

    fn dump(&mut self, msg: &str) {
        let Some(dir) = &self.dump_dir else { return };
        if self.dumps >= MAX_DUMPS {
            return;
        }
        self.dumps += 1;
        let mut out = format!(
            "{msg}\nsymbol {} tick {:?} step {:?}\nevents {} since start\n\n# last {} events (u, pu, U, bids, asks; ticks x lots)\n",
            self.symbol,
            self.spec.tick,
            self.spec.step,
            self.events,
            self.history.len()
        );
        let lv = |ls: &[Level]| -> String {
            ls.iter()
                .map(|l| format!("{}x{}", l.ticks, l.lots))
                .collect::<Vec<_>>()
                .join(" ")
        };
        for ev in &self.history {
            let _ = writeln!(
                out,
                "{} {} {} | {} | {}",
                ev.last_id,
                ev.prev_last_id,
                ev.first_id,
                lv(&ev.bids),
                lv(&ev.asks)
            );
        }
        for (name, side) in [("bids", Side::Bid), ("asks", Side::Ask)] {
            let _ = writeln!(
                out,
                "\n# BTreeMap {name}, best first\n{}",
                lv(&self.btree.all(side))
            );
            let _ = writeln!(
                out,
                "\n# glass-rs {name}, best first\n{}",
                lv(&self.glass.all(side))
            );
        }
        let path = dir.join(format!("mismatch-{}.txt", self.dumps));
        match std::fs::write(&path, out) {
            Ok(()) => eprintln!("wrote {}", path.display()),
            Err(e) => eprintln!("could not write {}: {e}", path.display()),
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fixed::Unit;

    fn app() -> App {
        let spec = SymbolSpec {
            tick: Unit::parse("0.1").unwrap(),
            step: Unit::parse("0.001").unwrap(),
        };
        App::offline("TEST".into(), spec, 1, false, None)
    }

    fn lvs(ls: &[(u32, u64)]) -> Vec<Level> {
        ls.iter()
            .map(|&(ticks, lots)| Level { ticks, lots })
            .collect()
    }

    /// A `depthUpdate` covering updates `first..=last`, after `pu`.
    fn ev(first: u64, last: u64, pu: u64, bids: &[(u32, u64)], asks: &[(u32, u64)]) -> DepthEvent {
        DepthEvent {
            first_id: first,
            last_id: last,
            prev_last_id: pu,
            bids: lvs(bids),
            asks: lvs(asks),
            received: Instant::now(),
        }
    }

    fn snap(id: u64, bids: &[(u32, u64)], asks: &[(u32, u64)]) -> Snapshot {
        Snapshot {
            last_update_id: id,
            bids: lvs(bids),
            asks: lvs(asks),
        }
    }

    type Side2 = Vec<(u32, u64)>;

    /// Both sides, best first, after checking the two books agree.
    fn book(app: &App) -> (Side2, Side2) {
        let side = |ls: Vec<Level>| ls.iter().map(|l| (l.ticks, l.lots)).collect::<Side2>();
        let b = (
            side(app.btree.all(Side::Bid)),
            side(app.btree.all(Side::Ask)),
        );
        let g = (
            side(app.glass.all(Side::Bid)),
            side(app.glass.all(Side::Ask)),
        );
        assert_eq!(b, g, "glass-rs and BTreeMap books differ");
        b
    }

    /// Snapshot at 100, then Binance's rules applied event by event; ends
    /// live at 110 with bids {99: 7, 97: 2}, asks {102: 9, 103: 1}.
    fn live_app() -> App {
        let mut app = app();
        app.load_snapshot(snap(100, &[(99, 5), (98, 3)], &[(101, 4), (102, 6)]));
        // u < lastUpdateId: older than the snapshot, dropped.
        app.handle(ev(90, 99, 89, &[(99, 1)], &[]));
        assert_eq!(
            book(&app),
            (vec![(99, 5), (98, 3)], vec![(101, 4), (102, 6)])
        );
        assert!(!app.live());
        // U <= lastUpdateId <= u: the first event applied. Quantities are
        // absolute (99 becomes 7, not 12); 0 deletes ask 101.
        app.handle(ev(95, 105, 99, &[(99, 7), (97, 2)], &[(101, 0)]));
        assert!(app.live());
        // Chained by pu. Deleting an absent level (96) is normal and a no-op.
        app.handle(ev(
            106,
            110,
            105,
            &[(98, 0), (96, 0)],
            &[(102, 9), (103, 1)],
        ));
        assert!(matches!(app.phase, Phase::Live(110)));
        assert_eq!(
            book(&app),
            (vec![(99, 7), (97, 2)], vec![(102, 9), (103, 1)])
        );
        app
    }

    #[test]
    fn sync_follows_binance_procedure() {
        let app = live_app();
        assert_eq!(app.events, 2);
        assert_eq!(app.check_failures, 0);
        // Best bid is the highest price, best ask the lowest.
        assert_eq!(
            app.spread().map(|(b, a)| (b.ticks, a.ticks)),
            Some((99, 102))
        );
        // Market orders walk from the best price: buy 10 = 9@102 + 1@103;
        // sell 8 = 7@99 + 1@97; an order past the book fills what there is.
        for b in [&app.btree as &dyn OrderBook, &app.glass] {
            assert_eq!(b.market(Side::Ask, 10), (9 * 102 + 103, 10));
            assert_eq!(b.market(Side::Bid, 8), (7 * 99 + 97, 8));
            assert_eq!(b.market(Side::Bid, 100), (7 * 99 + 2 * 97, 9));
        }
    }

    #[test]
    fn snapshot_older_than_stream_resyncs() {
        let mut app = app();
        app.load_snapshot(snap(100, &[(99, 5)], &[(101, 4)]));
        // The first event starts after the snapshot (U > lastUpdateId).
        app.handle(ev(101, 105, 100, &[(99, 1)], &[]));
        assert!(matches!(app.phase, Phase::Resync { .. }));
        assert_eq!(app.resyncs, 1);
        assert_eq!(
            app.pending.len(),
            1,
            "the event is kept for the next snapshot"
        );
        assert_eq!(
            book(&app),
            (vec![(99, 5)], vec![(101, 4)]),
            "books untouched"
        );
    }

    #[test]
    fn gap_resyncs_and_recovers() {
        let mut app = live_app();
        // pu 111 != 110: updates were missed.
        app.handle(ev(112, 115, 111, &[(99, 1)], &[]));
        assert!(matches!(app.phase, Phase::Resync { .. }));
        assert_eq!(
            book(&app),
            (vec![(99, 7), (97, 2)], vec![(102, 9), (103, 1)])
        );
        // The stream keeps coming while the new snapshot is fetched.
        app.pending
            .push_back(ev(116, 120, 115, &[(99, 3)], &[(102, 0)]));
        app.pending.push_back(ev(121, 125, 120, &[(98, 4)], &[]));
        app.load_snapshot(snap(118, &[(99, 2)], &[(102, 5), (104, 1)]));
        app.drain();
        // 112..115 dropped (older), 116..120 straddles 118, 121..125 chains.
        assert!(matches!(app.phase, Phase::Live(125)));
        assert_eq!(book(&app), (vec![(99, 3), (98, 4)], vec![(104, 1)]));
    }

    /// A full-depth snapshot vouches only for its own price range. The
    /// books re-sync on the update that leaves fewer than `MIN_KNOWN` known
    /// levels on a side, not later.
    #[test]
    fn resyncs_before_leaving_the_synced_reach() {
        let depth = crate::audit::SNAPSHOT_DEPTH as u32;
        let bids: Vec<(u32, u64)> = (0..depth).map(|i| (10_999 - i, 1)).collect();
        let asks: Vec<(u32, u64)> = (0..depth).map(|i| (20_000 + i, 1)).collect();
        let mut app = app();
        app.load_snapshot(snap(100, &bids, &asks));
        // The market falls through the top bids: delete all but MIN_KNOWN of
        // the snapshot's 1000 (the new top is still inside the reach).
        let keep = MIN_KNOWN as u32;
        let gone: Vec<(u32, u64)> = (10_000 + keep..=10_999).map(|t| (t, 0)).collect();
        app.handle(ev(95, 105, 99, &gone, &[]));
        assert!(matches!(app.phase, Phase::Live(105)));
        // One more level gone: MIN_KNOWN - 1 left, so take a new snapshot.
        app.handle(ev(106, 110, 105, &[(10_000 + keep - 1, 0)], &[]));
        assert!(matches!(app.phase, Phase::Resync { .. }));
        assert_eq!((app.resyncs, app.check_failures), (1, 0));
    }

    #[test]
    fn audit_exact_straddling_and_failing() {
        let mut app = live_app();
        // Snapshot exactly at the books' update id: exact comparison.
        app.begin_audit(snap(110, &[(99, 7), (97, 2)], &[(102, 9), (103, 1)]), 110);
        assert_eq!(
            (app.audits, app.audits_exact, app.audit_failures),
            (1, 1, 0)
        );
        // Snapshot at 112, inside the next event (110, 115]: bid 99 changed
        // in that event, so the exchange's 99@4 (its value at 112) is exempt.
        app.begin_audit(snap(112, &[(99, 4), (97, 2)], &[(102, 9), (103, 1)]), 110);
        assert!(app.audit.is_some(), "waits for the stream to reach 112");
        app.handle(ev(111, 115, 110, &[(99, 5)], &[]));
        assert_eq!(
            (app.audits, app.audits_exact, app.audit_failures),
            (2, 1, 0)
        );
        // A snapshot older than the books cannot be compared: skipped.
        app.begin_audit(snap(105, &[], &[]), 115);
        assert_eq!(app.audits_skipped, 1);
        // The exchange has no bid 97: a stale local level fails the audit
        // (in both books) and forces a resync.
        app.begin_audit(snap(115, &[(99, 5)], &[(102, 9), (103, 1)]), 115);
        assert_eq!(app.audit_failures, 1);
        assert!(matches!(app.phase, Phase::Resync { .. }));
        let msg = app.first_failure.as_deref().unwrap();
        assert!(
            msg.contains("BTreeMap bid 97: local Some(2) exchange None"),
            "{msg}"
        );
        assert!(msg.contains("glass-rs bid 97"), "{msg}");
    }
}
