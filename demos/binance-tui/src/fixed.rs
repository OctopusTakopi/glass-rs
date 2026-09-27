//! Exact decimal <-> integer conversion. Binance sends prices and sizes as
//! decimal strings; the book stores them as integer multiples of the symbol's
//! tick size / lot step, parsed without floating point so nothing rounds.

/// A tick size or lot step, e.g. `0.10` or `0.001`, as `unit * 10^-decimals`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Unit {
    decimals: u32,
    unit: u64,
}

impl Unit {
    /// Parses a positive decimal step like `"0.10"`.
    pub fn parse(s: &str) -> Option<Unit> {
        let decimals = s.split_once('.').map_or(0, |(_, f)| f.len()) as u32;
        let unit = scaled(s, decimals)?;
        (unit > 0).then_some(Unit { decimals, unit })
    }

    /// `s` as a whole number of units, or `None` if it is not an exact
    /// multiple (or is malformed).
    pub fn to_units(self, s: &str) -> Option<u64> {
        let v = scaled(s, self.decimals)?;
        (v % self.unit == 0).then(|| v / self.unit)
    }

    /// Exact decimal string for `n` units, with the unit's precision.
    pub fn format(self, n: u64) -> String {
        let v = n as u128 * self.unit as u128;
        if self.decimals == 0 {
            return v.to_string();
        }
        let p = 10u128.pow(self.decimals);
        format!("{}.{:0w$}", v / p, v % p, w = self.decimals as usize)
    }

    /// `n` units as a float, for display arithmetic only.
    pub fn to_f64(self, n: u64) -> f64 {
        n as f64 * self.unit as f64 / 10f64.powi(self.decimals as i32)
    }

    /// Value of one unit as a float.
    pub fn value(self) -> f64 {
        self.to_f64(1)
    }
}

/// `s` scaled by `10^decimals` (digits past `decimals` must be zero).
fn scaled(s: &str, decimals: u32) -> Option<u64> {
    let (int, frac) = s.split_once('.').unwrap_or((s, ""));
    if int.is_empty() || !int.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    let mut v: u64 = int.parse().ok()?;
    let fb = frac.as_bytes();
    if !fb.iter().all(|b| b.is_ascii_digit()) {
        return None;
    }
    for i in 0..decimals as usize {
        let d = fb.get(i).map_or(0, |c| c - b'0');
        v = v.checked_mul(10)?.checked_add(d as u64)?;
    }
    if fb.iter().skip(decimals as usize).any(|&c| c != b'0') {
        return None;
    }
    Some(v)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ticks_and_lots_round_trip() {
        let tick = Unit::parse("0.10").unwrap();
        assert_eq!(tick.to_units("84037.40"), Some(840374));
        assert_eq!(tick.to_units("84037.4"), Some(840374));
        assert_eq!(tick.to_units("84037.45"), None); // not a tick multiple
        assert_eq!(tick.format(840374), "84037.40");
        let step = Unit::parse("0.001").unwrap();
        assert_eq!(step.to_units("6.897"), Some(6897));
        assert_eq!(step.to_units("0.000"), Some(0));
        assert_eq!(step.format(6897), "6.897");
        let pepe = Unit::parse("0.0000001").unwrap();
        assert_eq!(pepe.to_units("0.0123456"), Some(123456));
        let whole = Unit::parse("1").unwrap();
        assert_eq!(whole.to_units("250"), Some(250));
        assert_eq!(whole.to_units("250.000"), Some(250));
        assert_eq!(whole.format(250), "250");
        assert_eq!(tick.to_units("-1"), None);
        assert_eq!(tick.to_units("1e3"), None);
    }

    /// 1000SATSUSDT: an 8-decimal tick and whole-coin lots in the tens of
    /// billions.
    #[test]
    fn tiny_prices_and_huge_sizes() {
        let tick = Unit::parse("0.00000001").unwrap();
        assert_eq!(tick.to_units("0.00001264"), Some(1264));
        assert_eq!(tick.to_units("0.0000126"), Some(1260));
        assert_eq!(tick.to_units("0.000012645"), None); // off the tick grid
        assert_eq!(tick.to_units("0.00001264000"), Some(1264));
        assert_eq!(tick.format(1264), "0.00001264");
        assert_eq!(tick.format(90_000_000), "0.90000000");
        let lot = Unit::parse("1").unwrap();
        assert_eq!(lot.to_units("50210000000"), Some(50_210_000_000));
        assert_eq!(lot.to_units("50210000000.5"), None);
        assert_eq!(lot.to_units("18446744073709551615"), Some(u64::MAX));
        assert_eq!(lot.to_units("18446744073709551616"), None); // past u64: rejected, no wrap
        assert_eq!(tick.to_units("184467440737.09551616"), None);
    }
}
