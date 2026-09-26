//! Two implementations of the same order book, fed identical updates:
//! a conventional `BTreeMap` book and a `glass_rs::Glass` book.
//!
//! Glass keeps its lowest 4096 keys in the fast trie, so its asks are keyed by
//! tick price and its bids by the bit-inverted tick price (`!ticks`): each
//! side's best level is its lowest key, so each side's top of book lives in
//! its trie.

use glass_rs::Glass;
use std::collections::BTreeMap;

/// One price level: absolute size `lots` at `ticks`; 0 removes the level.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Level {
    pub ticks: u32,
    pub lots: u64,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Side {
    Bid,
    Ask,
}

pub trait OrderBook {
    fn clear(&mut self);
    /// Sets the absolute size at a price; 0 removes the level.
    fn set(&mut self, side: Side, l: Level);
    fn best(&self, side: Side) -> Option<Level>;
    /// Best `n` levels of one side, best first, into `out`.
    fn top(&mut self, side: Side, n: usize, out: &mut Vec<Level>);
    /// `(bid levels, ask levels)`.
    fn levels(&self) -> (usize, usize);
    /// Market order of `lots` from the best price: `Σ ticks·lots` (saturating)
    /// and the lots filled.
    fn market(&self, side: Side, lots: u64) -> (u64, u64);
}

// ---------------------------------------------------------------- BTreeMap

#[derive(Default)]
pub struct BTreeBook {
    bids: BTreeMap<u32, u64>,
    asks: BTreeMap<u32, u64>,
}

impl OrderBook for BTreeBook {
    fn clear(&mut self) {
        self.bids.clear();
        self.asks.clear();
    }

    #[inline]
    fn set(&mut self, side: Side, l: Level) {
        let m = if side == Side::Ask {
            &mut self.asks
        } else {
            &mut self.bids
        };
        if l.lots == 0 {
            m.remove(&l.ticks);
        } else {
            m.insert(l.ticks, l.lots);
        }
    }

    fn best(&self, side: Side) -> Option<Level> {
        let kv = if side == Side::Ask {
            self.asks.first_key_value()
        } else {
            self.bids.last_key_value()
        };
        kv.map(|(&ticks, &lots)| Level { ticks, lots })
    }

    fn top(&mut self, side: Side, n: usize, out: &mut Vec<Level>) {
        out.clear();
        let lv = |(&ticks, &lots): (&u32, &u64)| Level { ticks, lots };
        if side == Side::Ask {
            out.extend(self.asks.iter().take(n).map(lv));
        } else {
            out.extend(self.bids.iter().rev().take(n).map(lv));
        }
    }

    fn levels(&self) -> (usize, usize) {
        (self.bids.len(), self.asks.len())
    }

    fn market(&self, side: Side, lots: u64) -> (u64, u64) {
        fn walk<'a>(it: impl Iterator<Item = (&'a u32, &'a u64)>, mut left: u64) -> (u64, u64) {
            let want = left;
            let mut cost = 0u64;
            for (&p, &q) in it {
                if left == 0 {
                    break;
                }
                let t = q.min(left);
                cost = cost.saturating_add((p as u64).saturating_mul(t));
                left -= t;
            }
            (cost, want - left)
        }
        if side == Side::Ask {
            walk(self.asks.iter(), lots)
        } else {
            walk(self.bids.iter().rev(), lots)
        }
    }
}

// ---------------------------------------------------------------- glass-rs

pub struct GlassBook {
    asks: Glass,
    bids: Glass, // keyed by !ticks
    // Total resting size per side, so a market-order estimate knows how much
    // actually fills (needed to undo the bid key inversion, see `market`).
    bid_lots: u64,
    ask_lots: u64,
    buf: Vec<(u32, u64)>,
}

impl Default for GlassBook {
    fn default() -> Self {
        GlassBook {
            asks: Glass::new(),
            bids: Glass::new(),
            bid_lots: 0,
            ask_lots: 0,
            buf: Vec::with_capacity(64),
        }
    }
}

impl OrderBook for GlassBook {
    fn clear(&mut self) {
        self.asks.clear();
        self.bids.clear();
        self.bid_lots = 0;
        self.ask_lots = 0;
    }

    #[inline]
    fn set(&mut self, side: Side, l: Level) {
        let (g, total, key) = match side {
            Side::Ask => (&mut self.asks, &mut self.ask_lots, l.ticks),
            Side::Bid => (&mut self.bids, &mut self.bid_lots, !l.ticks),
        };
        let old = g.get(key).unwrap_or(0);
        *total = *total - old + l.lots;
        g.insert(key, l.lots); // 0 deletes
    }

    fn best(&self, side: Side) -> Option<Level> {
        match side {
            Side::Ask => self.asks.min().map(|(k, q)| Level { ticks: k, lots: q }),
            Side::Bid => self.bids.min().map(|(k, q)| Level { ticks: !k, lots: q }),
        }
    }

    fn top(&mut self, side: Side, n: usize, out: &mut Vec<Level>) {
        let g = if side == Side::Ask {
            &self.asks
        } else {
            &self.bids
        };
        g.top_levels(n, &mut self.buf);
        out.clear();
        out.extend(self.buf.iter().map(|&(k, q)| Level {
            ticks: if side == Side::Ask { k } else { !k },
            lots: q,
        }));
    }

    fn levels(&self) -> (usize, usize) {
        (self.bids.len(), self.asks.len())
    }

    fn market(&self, side: Side, lots: u64) -> (u64, u64) {
        match side {
            Side::Ask => (self.asks.compute_buy_cost(lots), lots.min(self.ask_lots)),
            Side::Bid => {
                // Bids are keyed by !ticks = u32::MAX - ticks, so glass's
                // cheapest-first estimate over them is u32::MAX·filled − Σ ticks·lots.
                let filled = lots.min(self.bid_lots);
                let inverted = self.bids.compute_buy_cost(lots);
                ((u32::MAX as u64 * filled).saturating_sub(inverted), filled)
            }
        }
    }
}

impl GlassBook {
    /// Every level of one side, best first (for the full cross-check).
    pub fn all(&self, side: Side) -> Vec<Level> {
        match side {
            Side::Ask => self
                .asks
                .iter()
                .map(|(k, q)| Level { ticks: k, lots: q })
                .collect(),
            Side::Bid => self
                .bids
                .iter()
                .map(|(k, q)| Level { ticks: !k, lots: q })
                .collect(),
        }
    }
}

impl BTreeBook {
    pub fn all(&self, side: Side) -> Vec<Level> {
        let lv = |(&ticks, &lots): (&u32, &u64)| Level { ticks, lots };
        match side {
            Side::Ask => self.asks.iter().map(lv).collect(),
            Side::Bid => self.bids.iter().rev().map(lv).collect(),
        }
    }
}

/// Cross-checks the two books. `full` compares every level and market
/// estimates of several sizes (O(book)); otherwise only O(1) facts.
pub fn cross_check(g: &GlassBook, b: &BTreeBook, full: bool) -> Result<(), String> {
    if g.levels() != b.levels() {
        return Err(format!(
            "level counts glass {:?} != btree {:?}",
            g.levels(),
            b.levels()
        ));
    }
    for (side, name) in [(Side::Bid, "bid"), (Side::Ask, "ask")] {
        if g.best(side) != b.best(side) {
            return Err(format!(
                "best {name}: glass {:?} != btree {:?}",
                g.best(side),
                b.best(side)
            ));
        }
        if full {
            let (ga, ba) = (g.all(side), b.all(side));
            if let Some(i) = ga.iter().zip(&ba).position(|(x, y)| x != y) {
                return Err(format!(
                    "{name} level #{i}: glass {:?} != btree {:?}",
                    ga[i], ba[i]
                ));
            }
            for lots in [1, 100, 10_000, 1_000_000, u64::MAX] {
                if g.market(side, lots) != b.market(side, lots) {
                    return Err(format!(
                        "{name} market({lots}): glass {:?} != btree {:?}",
                        g.market(side, lots),
                        b.market(side, lots)
                    ));
                }
            }
        }
    }
    Ok(())
}
