//! Live Binance USDT-M perpetual order book, kept in a `BTreeMap` book and a
//! glass-rs book side by side from the same diff stream.
//!
//! ```text
//! binance-tui [SYMBOL] [--size LOTS] [--headless SECS] [--frame]
//! ```
//!
//! * `SYMBOL`: a USDT-M perpetual, default `BTCUSDT`.
//! * `--size LOTS`: market-order size for the estimates, in lot steps
//!   (default 1000, i.e. 1.000 BTC).
//! * `--headless SECS`: no terminal UI; run for SECS seconds, print a report,
//!   exit non-zero if the two books ever disagreed or the book crossed.
//! * `--frame`: with `--headless`, also print one rendered TUI frame.
//! * `--spin`: busy-poll the feed instead of sleeping between events, so the
//!   core stays hot (the usual setup for a latency-sensitive feed handler;
//!   pin it with `taskset`). Without it, each update lands on a cold cache
//!   and a clocked-down core.

mod app;
mod book;
mod feed;
mod fixed;
mod stats;
mod ui;

use app::App;
use crossterm::event::{self, Event, KeyCode, KeyEventKind};
use std::time::{Duration, Instant};

struct Args {
    symbol: String,
    size: u64,
    headless: Option<u64>,
    frame: bool,
    spin: bool,
}

fn parse_args() -> Result<Args, String> {
    let mut a = Args {
        symbol: "BTCUSDT".into(),
        size: 1000,
        headless: None,
        frame: false,
        spin: false,
    };
    let mut it = std::env::args().skip(1);
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "--size" => {
                a.size = it
                    .next()
                    .and_then(|v| v.parse().ok())
                    .ok_or("--size needs a number")?
            }
            "--headless" => {
                a.headless = Some(
                    it.next()
                        .and_then(|v| v.parse().ok())
                        .ok_or("--headless needs seconds")?,
                )
            }
            "--frame" => a.frame = true,
            "--spin" => a.spin = true,
            "-h" | "--help" => {
                return Err(
                    "usage: binance-tui [SYMBOL] [--size LOTS] [--headless SECS] [--frame] [--spin]".into(),
                );
            }
            s if !s.starts_with('-') => a.symbol = s.to_ascii_uppercase(),
            s => return Err(format!("unknown option {s}")),
        }
    }
    Ok(a)
}

fn main() {
    let result = parse_args().and_then(|args| {
        let app = App::new(args.symbol.clone(), args.size)?;
        match args.headless {
            Some(secs) => headless(app, secs, args.frame, args.spin),
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
            app.pump(Duration::from_millis(5))?;
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

fn headless(mut app: App, secs: u64, frame: bool, spin: bool) -> Result<(), String> {
    let end = Instant::now() + Duration::from_secs(secs);
    let mut next_report = Instant::now() + Duration::from_secs(5);
    let mut last_estimate = Instant::now();
    while Instant::now() < end {
        app.pump(Duration::from_millis(20))?;
        // Same cadence as the TUI's redraw, so estimates don't keep the book
        // artificially warm between updates.
        if last_estimate.elapsed() >= Duration::from_millis(50) {
            app.estimate();
            last_estimate = Instant::now();
        }
        if Instant::now() >= next_report {
            report(&app, false);
            next_report += Duration::from_secs(5);
        }
        if !spin {
            std::thread::sleep(Duration::from_millis(1));
        }
    }
    report(&app, true);
    if frame {
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
    if app.check_failures > 0 || app.crossed > 0 || app.events == 0 {
        return Err(format!(
            "FAILED: {} events, {} mismatches ({}), {} crossed",
            app.events,
            app.check_failures,
            app.first_failure.as_deref().unwrap_or("-"),
            app.crossed
        ));
    }
    Ok(())
}

fn report(app: &App, last: bool) {
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
    println!(
        "{}[{:>5.1}s] {} events, {} level updates, {} resyncs, {} checks ({} full), {} mismatches, {} crossed, levels {:?}",
        if last { "FINAL " } else { "" },
        app.started.elapsed().as_secs_f64(),
        app.events,
        app.level_updates,
        app.resyncs,
        app.checks,
        app.full_checks,
        app.check_failures,
        app.crossed,
        app.glass_levels(),
    );
    println!(
        "    BTreeMap : {} | {}",
        pct(&app.btree_stats),
        est(&app.btree_stats)
    );
    println!(
        "    glass-rs : {} | {}",
        pct(&app.glass_stats),
        est(&app.glass_stats)
    );
}
