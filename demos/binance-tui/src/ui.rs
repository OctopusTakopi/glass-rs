//! Side-by-side rendering: `BTreeMap` book on the left, glass-rs on the right.

use crate::app::{App, Impl};
use crate::book::{Level, OrderBook, Side};
use crate::fixed::Unit;
use ratatui::Frame;
use ratatui::layout::{Alignment, Constraint, Layout, Rect};
use ratatui::style::{Color, Modifier, Style, Stylize};
use ratatui::text::{Line, Span};
use ratatui::widgets::{Block, Cell, Paragraph, Row, Table};

pub fn draw(f: &mut Frame, app: &mut App) {
    let [header, body, footer] = Layout::vertical([
        Constraint::Length(3),
        Constraint::Min(10),
        Constraint::Length(1),
    ])
    .areas(f.area());
    draw_header(f, header, app);
    let [left, right] = Layout::horizontal([Constraint::Percentage(50); 2]).areas(body);
    let (tick, step) = (app.spec.tick, app.spec.step);
    let lots = app.market_lots;
    panel(
        f,
        left,
        &mut app.btree,
        &app.btree_stats,
        "BTreeMap  (std::collections)",
        Color::Yellow,
        tick,
        step,
        lots,
    );
    panel(
        f,
        right,
        &mut app.glass,
        &app.glass_stats,
        "glass-rs",
        Color::Cyan,
        tick,
        step,
        lots,
    );
    let keys = Line::from(vec![
        " q ".black().on_gray(),
        " quit  ".into(),
        " + / - ".black().on_gray(),
        format!(" market size ({})  ", step.format(lots)).into(),
    ]);
    f.render_widget(Paragraph::new(keys), footer);
}

fn draw_header(f: &mut Frame, area: Rect, app: &App) {
    let secs = app.started.elapsed().as_secs_f64().max(1e-9);
    let [q50, q99, _] = app.queue.percentiles();
    let check = if app.check_failures == 0 && app.exec_failures == 0 && app.audit_failures == 0 {
        Span::styled(
            format!(
                "books agree: {} checks ({} full), {} execution checks ({} ops), {} exchange audits, 0 mismatches",
                app.checks, app.full_checks, app.exec_checks, app.exec_ops, app.audits
            ),
            Style::new().fg(Color::Green),
        )
    } else {
        Span::styled(
            format!(
                "MISMATCH x{}: {}",
                app.check_failures + app.exec_failures + app.audit_failures,
                app.first_failure.as_deref().unwrap_or("")
            ),
            Style::new().fg(Color::Red).add_modifier(Modifier::BOLD),
        )
    };
    let spread = match app.spread() {
        Some((b, a)) => format!(
            "bid {} | ask {} | spread {}",
            app.spec.tick.format(b.ticks as u64),
            app.spec.tick.format(a.ticks as u64),
            app.spec
                .tick
                .format((a.ticks - b.ticks.min(a.ticks)) as u64)
        ),
        None => "no book yet".into(),
    };
    let lines = vec![
        Line::from(vec![
            format!(" {} USDT-M perpetual  ", app.symbol).bold(),
            Span::styled(
                format!("[{}]", app.status),
                Style::new().fg(if app.live() {
                    Color::Green
                } else {
                    Color::Yellow
                }),
            ),
            format!("  {spread}").into(),
        ]),
        Line::from(format!(
            " {} events ({:.1}/s), {} level updates, {} reconnects, {} resyncs, crossed {}, feed->book queue p50 {} p99 {}",
            app.events,
            app.events as f64 / secs,
            app.level_updates,
            app.reconnects,
            app.resyncs,
            app.crossed,
            ns(q50),
            ns(q99),
        )),
        Line::from(vec![" ".into(), check]),
    ];
    f.render_widget(Paragraph::new(lines).block(Block::new()), area);
}

#[allow(clippy::too_many_arguments)]
fn panel<B: OrderBook>(
    f: &mut Frame,
    area: Rect,
    book: &mut B,
    stats: &Impl,
    title: &str,
    color: Color,
    tick: Unit,
    step: Unit,
    market_lots: u64,
) {
    let block = Block::bordered().title(Span::styled(
        format!(" {title} "),
        Style::new().fg(color).bold(),
    ));
    let inner = block.inner(area);
    f.render_widget(block, area);
    let [info, ladder] = Layout::vertical([Constraint::Length(5), Constraint::Min(3)]).areas(inner);

    let (bids, asks) = book.levels();
    let [a50, a99, a999] = stats.apply.percentiles();
    let [e50, e99, _] = stats.estimate.percentiles();
    let mut lines = vec![
        Line::from(format!(" levels: {bids} bids / {asks} asks")),
        Line::from(vec![
            " apply per update: ".into(),
            Span::styled(
                format!(
                    "p50 {}  p99 {}  p99.9 {}  max {}",
                    ns(a50),
                    ns(a99),
                    ns(a999),
                    ns(stats.apply.max)
                ),
                Style::new().fg(color),
            ),
        ]),
        Line::from(vec![
            format!(" market {} buy+sell estimate: ", step.format(market_lots)).into(),
            Span::styled(
                format!("p50 {}  p99 {}", ns(e50), ns(e99)),
                Style::new().fg(color),
            ),
        ]),
    ];
    if let Some(((buy, bought), (sell, sold))) = stats.last_market {
        let vwap = |cost: u64, filled: u64| {
            if filled == 0 {
                "-".to_string()
            } else {
                format!(
                    "{:.*}",
                    decimals(tick),
                    cost as f64 / filled as f64 * tick.value()
                )
            }
        };
        lines.push(Line::from(format!(
            " buy {} @ vwap {}   sell {} @ vwap {}",
            step.format(bought),
            vwap(buy, bought),
            step.format(sold),
            vwap(sell, sold)
        )));
    }
    f.render_widget(Paragraph::new(lines), info);

    // Ladder: asks (worst..best) above the spread, bids (best..worst) below.
    let depth = ((ladder.height as usize).saturating_sub(2) / 2).max(1);
    let mut asks_top = Vec::new();
    let mut bids_top = Vec::new();
    book.top(Side::Ask, depth, &mut asks_top);
    book.top(Side::Bid, depth, &mut bids_top);
    let max_lots = asks_top
        .iter()
        .chain(&bids_top)
        .map(|l| l.lots)
        .max()
        .unwrap_or(1)
        .max(1);
    let bar_w = (ladder.width as usize).saturating_sub(34).clamp(4, 40);
    let row = |l: &Level, cum: u64, c: Color| {
        let bar = "█".repeat(((l.lots as u128 * bar_w as u128) / max_lots as u128) as usize);
        Row::new(vec![
            Cell::from(tick.format(l.ticks as u64)).style(Style::new().fg(c)),
            Cell::from(step.format(l.lots)),
            Cell::from(step.format(cum)).style(Style::new().fg(Color::DarkGray)),
            Cell::from(bar).style(Style::new().fg(c)),
        ])
    };
    let mut rows = Vec::new();
    let mut cum = 0;
    let ask_rows: Vec<Row> = asks_top
        .iter()
        .map(|l| {
            cum += l.lots;
            row(l, cum, Color::Red)
        })
        .collect();
    rows.extend(std::iter::repeat_n(
        Row::new(vec![""]),
        depth - asks_top.len(),
    ));
    rows.extend(ask_rows.into_iter().rev());
    let spread = match (bids_top.first(), asks_top.first()) {
        (Some(b), Some(a)) => format!(
            "spread {}",
            tick.format((a.ticks - b.ticks.min(a.ticks)) as u64)
        ),
        _ => String::new(),
    };
    rows.push(Row::new(vec![
        Cell::from(Line::from(spread).alignment(Alignment::Left))
            .style(Style::new().fg(Color::DarkGray)),
    ]));
    cum = 0;
    rows.extend(bids_top.iter().map(|l| {
        cum += l.lots;
        row(l, cum, Color::Green)
    }));
    let widths = [
        Constraint::Length(12),
        Constraint::Length(10),
        Constraint::Length(10),
        Constraint::Min(4),
    ];
    let table = Table::new(rows, widths)
        .header(
            Row::new(vec!["price", "size", "cum", ""])
                .style(Style::new().add_modifier(Modifier::UNDERLINED)),
        )
        .column_spacing(1);
    f.render_widget(table, ladder);
}

fn decimals(u: Unit) -> usize {
    u.format(1).split_once('.').map_or(0, |(_, f)| f.len())
}

fn ns(v: u64) -> String {
    match v {
        0..1_000 => format!("{v}ns"),
        1_000..1_000_000 => format!("{:.1}us", v as f64 / 1e3),
        _ => format!("{:.1}ms", v as f64 / 1e6),
    }
}
