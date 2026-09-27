//! L2 audit: the local books against Binance's own book.
//!
//! The per-update cross-check only shows that glass-rs and the `BTreeMap`
//! book agree; if the sync logic (or the reference book itself) were wrong,
//! both would be wrong together. So every few minutes the app fetches a fresh
//! REST snapshot, whose `lastUpdateId` L names an exact point in the update
//! stream, and compares the books with it when the stream reaches L:
//!
//! * an event ending exactly at L (`u == L`): the books must equal the
//!   snapshot exactly;
//! * an event straddling L (`pu < L < u`): its levels may legitimately hold
//!   either their value at L or their newer one, so those prices are exempt;
//!   every other level must match.
//!
//! Only prices both snapshots vouch for can be judged. A snapshot holds the
//! best 1000 levels by *count*, so its reach in price moves with the book:
//! when top levels go, it reaches deeper, into resting orders the local book
//! never saw (they predate its own sync snapshot and have not changed since,
//! so the stream never mentioned them). So the comparison covers bids down to
//! the higher of the two snapshots' lowest bids, asks up to the lower of their
//! highest asks; a snapshot shorter than 1000 levels holds its whole side.

use crate::book::{BTreeBook, GlassBook, Level, Side};
use crate::feed::Snapshot;
use std::collections::{BTreeMap, BTreeSet};

/// Levels per side the REST snapshot is requested with.
pub const SNAPSHOT_DEPTH: usize = 1000;

/// A snapshot waiting for the stream to reach its update id.
pub struct Pending {
    pub id: u64,
    bids: BTreeMap<u32, u64>,
    asks: BTreeMap<u32, u64>,
    reach: Reach,
}

/// The prices a snapshot vouches for: bids down to `bid_floor`, asks up to
/// `ask_ceiling` (`None`: the snapshot held the whole side).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Reach {
    pub bid_floor: Option<u32>,
    pub ask_ceiling: Option<u32>,
}

impl Reach {
    pub fn of(snap: &Snapshot) -> Reach {
        let full = |ls: &[Level]| ls.len() >= SNAPSHOT_DEPTH;
        Reach {
            bid_floor: if full(&snap.bids) {
                snap.bids.iter().map(|l| l.ticks).min()
            } else {
                None
            },
            ask_ceiling: if full(&snap.asks) {
                snap.asks.iter().map(|l| l.ticks).max()
            } else {
                None
            },
        }
    }

    /// Prices both reaches vouch for.
    fn and(self, other: Reach) -> Reach {
        Reach {
            bid_floor: self.bid_floor.max(other.bid_floor),
            ask_ceiling: match (self.ask_ceiling, other.ask_ceiling) {
                (Some(a), Some(b)) => Some(a.min(b)),
                (a, b) => a.or(b),
            },
        }
    }
}

impl Pending {
    pub fn new(snap: &Snapshot) -> Pending {
        let map = |ls: &[Level]| ls.iter().map(|l| (l.ticks, l.lots)).collect();
        Pending {
            id: snap.last_update_id,
            bids: map(&snap.bids),
            asks: map(&snap.asks),
            reach: Reach::of(snap),
        }
    }
}

/// Levels where `book` (best first, as `all` returns it) differs from the
/// snapshot within the snapshot's range, ignoring `exempt` prices; and how
/// many prices were compared.
fn side_diff(
    book: &[Level],
    snap: &BTreeMap<u32, u64>,
    in_range: impl Fn(u32) -> bool,
    exempt: &BTreeSet<u32>,
) -> (Vec<String>, usize) {
    let local: BTreeMap<u32, u64> = book
        .iter()
        .filter(|l| in_range(l.ticks))
        .map(|l| (l.ticks, l.lots))
        .collect();
    let prices: BTreeSet<u32> = local
        .keys()
        .chain(snap.keys().filter(|&&p| in_range(p)))
        .copied()
        .collect();
    let judged: Vec<u32> = prices.into_iter().filter(|p| !exempt.contains(p)).collect();
    let diffs = judged
        .iter()
        .filter_map(|p| {
            let (ours, theirs) = (local.get(p), snap.get(p));
            (ours != theirs).then(|| format!("{p}: local {ours:?} exchange {theirs:?}"))
        })
        .collect();
    (diffs, judged.len())
}

/// Every difference between a book, synced from a snapshot with reach
/// `synced`, and the audit snapshot, as `"<book> <side> <price>: ..."`
/// lines; and the number of price levels judged (per book).
pub fn diff(
    btree: &BTreeBook,
    glass: &GlassBook,
    synced: Reach,
    p: &Pending,
    exempt_bids: &BTreeSet<u32>,
    exempt_asks: &BTreeSet<u32>,
) -> (Vec<String>, usize) {
    let mut out = Vec::new();
    let mut judged = 0;
    let reach = p.reach.and(synced);
    let floor = reach.bid_floor.unwrap_or(0);
    let ceiling = reach.ask_ceiling.unwrap_or(u32::MAX);
    for (name, bids, asks) in [
        ("BTreeMap", btree.all(Side::Bid), btree.all(Side::Ask)),
        ("glass-rs", glass.all(Side::Bid), glass.all(Side::Ask)),
    ] {
        let (bid_diffs, nb) = side_diff(&bids, &p.bids, |t| t >= floor, exempt_bids);
        let (ask_diffs, na) = side_diff(&asks, &p.asks, |t| t <= ceiling, exempt_asks);
        out.extend(bid_diffs.into_iter().map(|d| format!("{name} bid {d}")));
        out.extend(ask_diffs.into_iter().map(|d| format!("{name} ask {d}")));
        judged = nb + na;
    }
    (out, judged)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::book::OrderBook;

    fn lv(ticks: u32, lots: u64) -> Level {
        Level { ticks, lots }
    }

    fn books(bids: &[Level], asks: &[Level]) -> (BTreeBook, GlassBook) {
        let (mut b, mut g) = (BTreeBook::default(), GlassBook::default());
        for &l in bids {
            b.set(Side::Bid, l);
            g.set(Side::Bid, l);
        }
        for &l in asks {
            b.set(Side::Ask, l);
            g.set(Side::Ask, l);
        }
        (b, g)
    }

    fn snap(id: u64, bids: Vec<Level>, asks: Vec<Level>) -> Pending {
        Pending::new(&Snapshot {
            last_update_id: id,
            bids,
            asks,
        })
    }

    #[test]
    fn equal_books_pass() {
        let (b, g) = books(&[lv(99, 5), lv(98, 3)], &[lv(101, 4)]);
        let p = snap(7, vec![lv(99, 5), lv(98, 3)], vec![lv(101, 4)]);
        assert!(
            diff(
                &b,
                &g,
                Reach::default(),
                &p,
                &BTreeSet::new(),
                &BTreeSet::new()
            )
            .0
            .is_empty()
        );
    }

    #[test]
    fn stale_missing_and_wrong_levels_fail_in_both_books() {
        // Local has a stale bid 97 and a wrong ask size; misses bid 96.
        let (b, g) = books(&[lv(99, 5), lv(97, 1)], &[lv(101, 4)]);
        let p = snap(7, vec![lv(99, 5), lv(96, 2)], vec![lv(101, 3)]);
        let (d, judged) = diff(
            &b,
            &g,
            Reach::default(),
            &p,
            &BTreeSet::new(),
            &BTreeSet::new(),
        );
        assert_eq!(judged, 4, "bids 96, 97, 99 and ask 101");
        assert_eq!(
            d,
            [
                "BTreeMap bid 96: local None exchange Some(2)",
                "BTreeMap bid 97: local Some(1) exchange None",
                "BTreeMap ask 101: local Some(4) exchange Some(3)",
                "glass-rs bid 96: local None exchange Some(2)",
                "glass-rs bid 97: local Some(1) exchange None",
                "glass-rs ask 101: local Some(4) exchange Some(3)",
            ]
        );
    }

    #[test]
    fn exempt_prices_are_skipped() {
        let (b, g) = books(&[lv(99, 5)], &[lv(101, 4)]);
        let p = snap(7, vec![lv(99, 9)], vec![lv(101, 4)]);
        let exempt: BTreeSet<u32> = [99].into();
        assert!(
            diff(&b, &g, Reach::default(), &p, &exempt, &BTreeSet::new())
                .0
                .is_empty()
        );
    }

    #[test]
    fn only_the_snapshot_range_is_judged() {
        // A full-depth snapshot: bids 10_001..=11_000, asks 20_000..=20_999.
        let bids: Vec<Level> = (0..SNAPSHOT_DEPTH as u32)
            .map(|i| lv(11_000 - i, 1))
            .collect();
        let asks: Vec<Level> = (0..SNAPSHOT_DEPTH as u32)
            .map(|i| lv(20_000 + i, 1))
            .collect();
        let p = snap(7, bids.clone(), asks.clone());
        // Local also holds levels past both ends (deeper than the snapshot).
        let (b, g) = books(
            &[bids.as_slice(), &[lv(5, 1), lv(10_000, 2)]].concat(),
            &[asks.as_slice(), &[lv(21_000, 3)]].concat(),
        );
        assert!(
            diff(
                &b,
                &g,
                Reach::default(),
                &p,
                &BTreeSet::new(),
                &BTreeSet::new()
            )
            .0
            .is_empty()
        );
        // Nor what the local book's own sync snapshot did not reach: here
        // it reached bids down to 10_500 and asks up to 20_400 only, so a
        // level the book never saw (bid 10_200) is not held against it.
        let synced = Reach {
            bid_floor: Some(10_500),
            ask_ceiling: Some(20_400),
        };
        let partial: Vec<Level> = bids.iter().copied().filter(|l| l.ticks != 10_200).collect();
        let (b, g) = books(&partial, &asks);
        assert!(
            diff(&b, &g, synced, &p, &BTreeSet::new(), &BTreeSet::new())
                .0
                .is_empty()
        );
        // ...but it is within the full reach.
        assert_eq!(
            diff(
                &b,
                &g,
                Reach::default(),
                &p,
                &BTreeSet::new(),
                &BTreeSet::new()
            )
            .0
            .len(),
            2
        );
        // A short snapshot vouches for its whole side: the extra level counts.
        let p = snap(7, vec![lv(99, 5)], vec![lv(101, 4)]);
        let (b, g) = books(&[lv(99, 5), lv(5, 1)], &[lv(101, 4)]);
        assert_eq!(
            diff(
                &b,
                &g,
                Reach::default(),
                &p,
                &BTreeSet::new(),
                &BTreeSet::new()
            )
            .0
            .len(),
            2
        );
    }
}
