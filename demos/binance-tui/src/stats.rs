//! Rolling latency window with percentiles.

pub struct Latency {
    buf: Vec<u32>,
    pos: usize,
    pub count: u64,
    pub max: u64,
}

const WINDOW: usize = 20_000;

impl Default for Latency {
    fn default() -> Self {
        Latency {
            buf: Vec::with_capacity(WINDOW),
            pos: 0,
            count: 0,
            max: 0,
        }
    }
}

impl Latency {
    pub fn record(&mut self, ns: u64) {
        let v = ns.min(u32::MAX as u64) as u32;
        if self.buf.len() < WINDOW {
            self.buf.push(v);
        } else {
            self.buf[self.pos] = v;
            self.pos = (self.pos + 1) % WINDOW;
        }
        self.count += 1;
        self.max = self.max.max(ns);
    }

    /// `[p50, p99, p99.9]` over the window (ns), or zeros when empty.
    pub fn percentiles(&self) -> [u64; 3] {
        if self.buf.is_empty() {
            return [0; 3];
        }
        let mut v = self.buf.clone();
        v.sort_unstable();
        let at = |q: f64| v[((v.len() - 1) as f64 * q) as usize] as u64;
        [at(0.50), at(0.99), at(0.999)]
    }
}
