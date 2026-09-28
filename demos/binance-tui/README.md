# binance-tui

A live Binance USDT-M perpetual order book in the terminal, kept twice from
the same diff stream: a conventional `BTreeMap` book on the left and a
glass-rs book on the right. Each panel shows its own per-update apply
latency and a timed market-order estimate. The header cross-checks the two
books on every update (a full level-by-level and estimate comparison every
16 updates) and turns red on any disagreement.

```sh
cd demos/binance-tui
cargo run --release -- BTCUSDT            # q quits, +/- change the market-order size
cargo run --release -- ETHUSDT --spin     # busy-poll: lower, steadier latency

# no terminal: run 60 s, print a report (+ one rendered frame), exit 3 if
# the books ever disagreed
cargo run --release -- BTCUSDT --headless 60 --frame
```

Sync follows Binance's documented diff-depth procedure: buffer the
`<symbol>@depth@100ms` stream, take a REST snapshot, drop events older than
its `lastUpdateId`, require the first event to straddle it, check each
event's `pu` against the previous `u`, and resync on any gap. Prices and
sizes are parsed from Binance's decimal strings to integer ticks/lots
exactly (no floats). Asks are keyed by tick price and bids by the
bit-inverted tick price, so each side's best levels live in glass's fast
trie.

Besides the per-update cross-check, every 10 s an *execution check* copies
each side of the live book into a fresh glass and a `BTreeMap` oracle and
runs 200 random operations on both, comparing every result: market buys and
sells (`buy_shares`/`sell_shares`), `remove_by_index`, `pop_first`/`pop_last`,
`update_value`, `next_level`/`prev_level`, `range`, cost estimates, inserts and
removes. The live feed only drives inserts, removes and lookups; this puts
real market-shaped data through the rest of the API.

Agreement between the two books says nothing about the L2 book itself: if
the sync logic were wrong, both would be wrong together. So every 5 minutes
an *exchange audit* fetches a fresh REST snapshot and compares both books
with it once the stream reaches the snapshot's `lastUpdateId`: exactly, if
an event ends there; otherwise with the levels of the event that straddles
it exempt (they may hold any value from inside that event). Only prices both
the audit snapshot and the books' own sync snapshot reach are judged: a
snapshot holds the best 1000 levels by count, so as the book moves it reaches
resting orders the local book never saw.

Binance's procedure takes one snapshot, plus a new one after a gap. That
leaves the book incomplete beyond the snapshot's reach: an order resting
there since before the sync, unchanged since, is never sent by the stream,
and stays unknown when the price moves to it (Binance's spot docs note the
same). BTC's 1000 levels span only ~$100-300 a side, so over a day the
price leaves that range many times. The app therefore also re-syncs, checked
on every update, once fewer than 300 levels on a side remain inside the
reach of the snapshot it synced from, so the top of the book never leaves the
region it knows (one REST call, weight 20, each time; BTC needed ~100 a day). The sync procedure, both books' L2 semantics and the audit have unit
tests with hand-computed books (`cargo test`).

## Running unattended

No network failure stops it. Every connect, TLS/WebSocket handshake and REST
call has a deadline, and a connection that delivers no depth data for 60 s
counts as dead (Binance only pings every 3 minutes, and a half-open TCP
connection otherwise blocks forever). A dropped stream reconnects (Binance
also closes every connection after 24 h), and a gap or a snapshot that lags the
stream resyncs. Each waits out an exponential back-off (1 s doubling to
5 min, or the server's `Retry-After` on HTTP 429/418), and the streak resets
after 600 live updates. The tick/lot grid is re-read on every reconnect,
since Binance does change it.

A disagreement between the books is logged, its evidence (the last 256
updates and both books in full) written to `--state-dir`, and the books
rebuilt from a fresh snapshot, so later checks still mean something. A
crossed book is reported but is not a failure: it is feed data that both
books agree on.

`deploy/glass-binance@.service` runs it headless under systemd, one
instance per symbol (`glass-binance@BTCUSDT`, `glass-binance@1000SATSUSDT`),
each until its own deadline:

```sh
binance-tui BTCUSDT --until $(date -d '+7 days' +%s) --report-every 60 \
    --state-dir /var/lib/glass-binance-BTCUSDT
```

Low-priced coins with huge sizes are worth running alongside BTC. 1000SATS
trades at ~0.00001 USDT in whole-coin lots, ~1e11 lots per side, so its
integer sums leave the range BTC's books ever reach: `u32::MAX × lots` and
glass's bid-side sums (keys `!ticks` ~ 4.3e9) pass `u64`, exercising the
saturating arithmetic. The full check compares glass's `compute_buy_cost` /
`compute_sell_cost` in its own key space against an exact `u128` oracle at
order sizes up to 1e12 lots (4e9 lots lands just under `u64::MAX`).

Test hooks: `BINANCE_TUI_REST` / `BINANCE_TUI_WS` override the endpoints, and
`BINANCE_TUI_CHAOS_SECS=N` drops each stream connection after N seconds.

## Measuring it

`--spin` keeps the book thread hot. Give the feed thread its own core: with
the whole process pinned to one core (`taskset -c 30`), every message
preempts the spinning book thread, and the tail absorbs the context switch.
Use two physical cores (`taskset -c 30,31`).

BTCUSDT, 45 s live, 431 updates (~83 levels each), `--spin`, `taskset -c
30,31`, Xeon Gold 6230: 0 mismatches over 431 checks (26 full), 0 crossed.

| per update       | p50     | p99     | p99.9   | max     |
|------------------|---------|---------|---------|---------|
| BTreeMap apply   | 5.36 us | 31.4 us | 44.3 us | 53.6 us |
| glass-rs apply   | 2.65 us | 20.7 us | 31.4 us | 33.4 us |
| BTreeMap 1-BTC buy+sell estimate | 101 ns | 1148 ns |  |  |
| glass-rs 1-BTC buy+sell estimate |  60 ns |  594 ns |  |  |

An Intel PT trace (trace-mcp) of the slowest update in
a run (404 levels, 61 us, sleeping mode) shows ~150 instructions per level
at IPC ~0.36. That is two hash-table lookups (the demo reads the old size
before writing the new one), the leaf update and the ancestor counts: glass
does little work per level and waits on memory. BTC's deep levels are
sparse at a 0.1 tick, so the book needs close to one leaf per level
(~1 MB), and scattered updates miss in L2. No unexpected paths ran: no
restructure, no trie fallback lookup, no overflow tier. New-leaf creation
and best-level re-finding appear, rarely, as expected.
