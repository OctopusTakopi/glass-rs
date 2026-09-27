//! Live Binance USDT-M perpetual order book, kept in a `BTreeMap` book and a
//! glass-rs book side by side from the same diff stream.
//!
//! ```text
//! binance-tui [SYMBOL] [--size LOTS] [--spin]
//!             [--headless SECS | --until UNIX_SECS] [--report-every SECS]
//!             [--state-dir DIR] [--frame]
//! ```
//!
//! * `SYMBOL`: a USDT-M perpetual, default `BTCUSDT`.
//! * `--size LOTS`: market-order size for the estimates, in lot steps
//!   (default 1000, i.e. 1.000 BTC).
//! * `--headless SECS`: no terminal UI; run for SECS seconds (or until
//!   SIGINT/SIGTERM), print a report, and exit with status 3 if the two books
//!   ever disagreed or the execution check failed.
//! * `--until UNIX_SECS`: headless, until a wall-clock deadline, so a
//!   restarted service keeps the original end time.
//! * `--report-every SECS`: headless report interval (default 5).
//! * `--state-dir DIR`: headless; keep the latest report in `DIR/report.txt`
//!   and write the evidence of any disagreement to `DIR/mismatch-N.txt`.
//! * `--frame`: with `--headless`, also print one rendered TUI frame.
//! * `--spin`: busy-poll the feed instead of sleeping between events, so the
//!   core stays hot (the usual setup for a latency-sensitive feed handler;
//!   pin it with `taskset`). Without it, each update lands on a cold cache
//!   and a clocked-down core.

mod app;
mod audit;
mod book;
mod feed;
mod fixed;
mod stats;
mod ui;

use app::{App, STOP};
use crossterm::event::{self, Event, KeyCode, KeyEventKind};
use std::path::PathBuf;
use std::sync::atomic::Ordering;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

/// Exit status when the books disagreed (distinct from startup errors, so a
/// service manager can tell a verdict from a crash).
const EXIT_MISMATCH: i32 = 3;

const USAGE: &str = "usage: binance-tui [SYMBOL] [--size LOTS] [--spin] \
[--headless SECS | --until UNIX_SECS] [--report-every SECS] [--state-dir DIR] [--frame]";

struct Args {
    symbol: String,
    size: u64,
    headless: Option<u64>,
    report_every: u64,
    state_dir: Option<PathBuf>,
    frame: bool,
    spin: bool,
}

fn parse_args() -> Result<Args, String> {
    let mut a = Args {
        symbol: "BTCUSDT".into(),
        size: 1000,
        headless: None,
        report_every: 5,
        state_dir: None,
        frame: false,
        spin: false,
    };
    let mut it = std::env::args().skip(1);
    let num = |it: &mut std::iter::Skip<std::env::Args>, what: &str| -> Result<u64, String> {
        it.next()
            .and_then(|v| v.parse().ok())
            .ok_or(format!("{what} needs a number"))
    };
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "--size" => a.size = num(&mut it, "--size")?,
            "--headless" => a.headless = Some(num(&mut it, "--headless")?),
            "--until" => {
                let until = num(&mut it, "--until")?;
                let now = SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .map_or(0, |d| d.as_secs());
                a.headless = Some(until.saturating_sub(now));
            }
            "--report-every" => a.report_every = num(&mut it, "--report-every")?.max(1),
            "--state-dir" => {
                a.state_dir = Some(it.next().ok_or("--state-dir needs a path")?.into())
            }
            "--frame" => a.frame = true,
            "--spin" => a.spin = true,
            "-h" | "--help" => return Err(USAGE.into()),
            s if !s.starts_with('-') => a.symbol = s.to_ascii_uppercase(),
            s => return Err(format!("unknown option {s}")),
        }
    }
    Ok(a)
}

fn main() {
    // SIGINT/SIGTERM: finish the current step, report, and exit. (In the TUI,
    // raw mode delivers Ctrl-C as a key instead.)
    if let Err(e) = ctrlc::set_handler(|| STOP.store(true, Ordering::Relaxed)) {
        eprintln!("binance-tui: no signal handler ({e}); SIGTERM will skip the final report");
    }
    let result = parse_args().and_then(|args| {
        if args.headless == Some(0) {
            // E.g. a service started (at boot) after its `--until` deadline:
            // the run is over, and failing would only get it restarted.
            eprintln!("binance-tui: headless deadline already passed; nothing to do");
            return Ok(());
        }
        let headless_run = args.headless.is_some();
        let app = App::new(
            args.symbol.clone(),
            args.size,
            headless_run,
            args.state_dir.clone(),
        )?;
        match args.headless {
            Some(secs) => headless(app, secs, &args),
            None => tui(app, args.spin),
        }
    });
    if let Err(e) = result {
        eprintln!("binance-tui: {e}");
        std::process::exit(1);
    }
}

fn tui(mut app: App, spin: bool) -> Result<(), String> {
    let key_wait = if spin {
        Duration::ZERO
    } else {
        Duration::from_millis(2)
    };
    let mut terminal = ratatui::init();
    let res = (|| -> Result<(), String> {
        let mut last_draw = Instant::now() - Duration::from_secs(1);
        loop {
            app.pump(Duration::from_millis(5));
            if last_draw.elapsed() >= Duration::from_millis(50) {
                app.estimate();
                terminal
                    .draw(|f| ui::draw(f, &mut app))
                    .map_err(|e| e.to_string())?;
                last_draw = Instant::now();
            }
            if event::poll(key_wait).map_err(|e| e.to_string())?
                && let Event::Key(k) = event::read().map_err(|e| e.to_string())?
                && k.kind == KeyEventKind::Press
            {
                match k.code {
                    KeyCode::Char('q') | KeyCode::Esc => return Ok(()),
                    KeyCode::Char('+') | KeyCode::Char('=') => {
                        app.market_lots = app.market_lots.saturating_mul(2)
                    }
                    KeyCode::Char('-') => app.market_lots = (app.market_lots / 2).max(1),
                    _ => {}
                }
            }
        }
    })();
    ratatui::restore();
    res
}

fn headless(mut app: App, secs: u64, args: &Args) -> Result<(), String> {
    if let Some(dir) = &args.state_dir {
        std::fs::create_dir_all(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    }
    let every = Duration::from_secs(args.report_every);
    let end = Instant::now() + Duration::from_secs(secs);
    let mut next_report = Instant::now() + every;
    let mut last_estimate = Instant::now();
    while Instant::now() < end && !STOP.load(Ordering::Relaxed) {
        app.pump(Duration::from_millis(20));
        // Same cadence as the TUI's redraw, so estimates don't keep the book
        // artificially warm between updates.
        if last_estimate.elapsed() >= Duration::from_millis(50) {
            app.estimate();
            last_estimate = Instant::now();
        }
        if Instant::now() >= next_report {
            report(&app, false, args.state_dir.as_ref());
            next_report += every;
        }
        if !args.spin {
            std::thread::sleep(Duration::from_millis(1));
        }
    }
    report(&app, true, args.state_dir.as_ref());
    if args.frame {
        let mut t = ratatui::Terminal::new(ratatui::backend::TestBackend::new(160, 40))
            .map_err(|e| e.to_string())?;
        t.draw(|f| ui::draw(f, &mut app))
            .map_err(|e| e.to_string())?;
        let buf = t.backend().buffer();
        for y in 0..buf.area.height {
            let line: String = (0..buf.area.width).map(|x| buf[(x, y)].symbol()).collect();
            println!("{}", line.trim_end());
        }
    }
    // The verdict: glass-rs agreed with the BTreeMap book, and both agreed
    // with the exchange. A crossed book is feed data both books agree on; it
    // is reported above.
    if app.check_failures > 0 || app.exec_failures > 0 || app.audit_failures > 0 {
        eprintln!(
            "FAILED: {} book mismatches, {} execution-check failures, {} exchange-audit failures; first: {}",
            app.check_failures,
            app.exec_failures,
            app.audit_failures,
            app.first_failure.as_deref().unwrap_or("-"),
        );
        std::process::exit(EXIT_MISMATCH);
    }
    if app.events == 0 && !STOP.load(Ordering::Relaxed) {
        return Err("no events received".into());
    }
    Ok(())
}

fn report(app: &App, last: bool, state_dir: Option<&PathBuf>) {
    let pct = |s: &app::Impl| {
        let [p50, p99, p999] = s.apply.percentiles();
        format!(
            "apply p50 {p50}ns p99 {p99}ns p99.9 {p999}ns max {}ns",
            s.apply.max
        )
    };
    let est = |s: &app::Impl| {
        let [p50, p99, _] = s.estimate.percentiles();
        format!("estimate p50 {p50}ns p99 {p99}ns")
    };
    let text = format!(
        "{}[{:.0}s] {} | {} events, {} level updates | {} checks ({} full), {} mismatches | \
{} exec checks ({} ops), {} exec failures | {} audits ({} exact, {} levels), {} skipped, {} audit failures | \
{} reconnects, {} resyncs, {} snapshots | \
crossed {} events ({} onsets) | levels {:?}\n    BTreeMap : {} | {}\n    glass-rs : {} | {}\n",
        if last { "FINAL " } else { "" },
        app.started.elapsed().as_secs_f64(),
        if app.live() { "live" } else { "syncing" },
        app.events,
        app.level_updates,
        app.checks,
        app.full_checks,
        app.check_failures,
        app.exec_checks,
        app.exec_ops,
        app.exec_failures,
        app.audits,
        app.audits_exact,
        app.audit_levels,
        app.audits_skipped,
        app.audit_failures,
        app.reconnects,
        app.resyncs,
        app.snapshots,
        app.crossed,
        app.cross_onsets,
        app.glass_levels(),
        pct(&app.btree_stats),
        est(&app.btree_stats),
        pct(&app.glass_stats),
        est(&app.glass_stats),
    );
    print!("{text}");
    if let Some(dir) = state_dir {
        // Write-then-rename, so a reader never sees half a report.
        let (tmp, dst) = (dir.join("report.txt.tmp"), dir.join("report.txt"));
        let first = app.first_failure.as_deref().unwrap_or("none");
        let body = format!("{text}first failure: {first}\n");
        if let Err(e) = std::fs::write(&tmp, body).and_then(|()| std::fs::rename(&tmp, &dst)) {
            eprintln!("could not write {}: {e}", dst.display());
        }
    }
}
