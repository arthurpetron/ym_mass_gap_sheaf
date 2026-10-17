//! Shared pieces: xoshiro256** RNG, 4D periodic lattice geometry, tiny CLI parser.
//! No external crates (offline-buildable). MC measurement code only.

pub struct Rng {
    pub s: [u64; 4],
}

fn splitmix(x: &mut u64) -> u64 {
    *x = x.wrapping_add(0x9E3779B97F4A7C15);
    let mut z = *x;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
    z ^ (z >> 31)
}

impl Rng {
    pub fn new(seed: u64) -> Self {
        let mut x = seed;
        Rng { s: [splitmix(&mut x), splitmix(&mut x), splitmix(&mut x), splitmix(&mut x)] }
    }
    #[inline]
    pub fn next_u64(&mut self) -> u64 {
        let s = &mut self.s;
        let r = s[1].wrapping_mul(5).rotate_left(7).wrapping_mul(9);
        let t = s[1] << 17;
        s[2] ^= s[0];
        s[3] ^= s[1];
        s[1] ^= s[2];
        s[0] ^= s[3];
        s[2] ^= t;
        s[3] = s[3].rotate_left(45);
        r
    }
    /// uniform in the open interval (0,1)
    #[inline]
    pub fn uni(&mut self) -> f64 {
        ((self.next_u64() >> 11) as f64 + 0.5) * (1.0 / 9007199254740992.0)
    }
}

pub struct Geom {
    pub l: usize,
    pub vol: usize,
    pub up: Vec<[usize; 4]>,
    pub dn: Vec<[usize; 4]>,
}

impl Geom {
    pub fn new(l: usize) -> Self {
        let vol = l * l * l * l;
        let mut up = vec![[0usize; 4]; vol];
        let mut dn = vec![[0usize; 4]; vol];
        for s in 0..vol {
            let mut c = [0usize; 4];
            let mut r = s;
            for m in 0..4 {
                c[m] = r % l;
                r /= l;
            }
            for m in 0..4 {
                let idx = |cc: &[usize; 4]| ((cc[3] * l + cc[2]) * l + cc[1]) * l + cc[0];
                let mut cu = c;
                cu[m] = (c[m] + 1) % l;
                let mut cd = c;
                cd[m] = (c[m] + l - 1) % l;
                up[s][m] = idx(&cu);
                dn[s][m] = idx(&cd);
            }
        }
        Geom { l, vol, up, dn }
    }
}

/// minimal `--key value` parser
pub struct Args {
    pub kv: std::collections::HashMap<String, String>,
}
impl Args {
    pub fn parse() -> Self {
        let a: Vec<String> = std::env::args().skip(1).collect();
        let mut kv = std::collections::HashMap::new();
        let mut i = 0;
        while i < a.len() {
            if let Some(k) = a[i].strip_prefix("--") {
                let v = if i + 1 < a.len() && !a[i + 1].starts_with("--") { i += 1; a[i].clone() } else { "1".to_string() };
                kv.insert(k.to_string(), v);
            }
            i += 1;
        }
        Args { kv }
    }
    pub fn get<T: std::str::FromStr>(&self, k: &str, d: T) -> T {
        self.kv.get(k).and_then(|v| v.parse().ok()).unwrap_or(d)
    }
    pub fn gets(&self, k: &str, d: &str) -> String {
        self.kv.get(k).cloned().unwrap_or(d.to_string())
    }
}

/// flow-time list: c-values -> t = c^2 L^2 / 8, plus explicit extra times; sorted, deduplicated
pub fn flow_times(l: usize, cs: &str, extra: &str) -> Vec<f64> {
    let mut v: Vec<f64> = vec![];
    for c in cs.split(',').filter(|s| !s.is_empty()) {
        let c: f64 = c.parse().unwrap();
        v.push(c * c * (l * l) as f64 / 8.0);
    }
    for t in extra.split(',').filter(|s| !s.is_empty()) {
        v.push(t.parse().unwrap());
    }
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    v.dedup_by(|a, b| (*a - *b).abs() < 1e-12);
    v
}
