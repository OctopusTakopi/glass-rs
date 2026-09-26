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

# no terminal: run 60 s, print a report (+ one rendered frame), exit non-zero
# if the books ever disagreed or the book crossed
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
