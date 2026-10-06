//! P4 (YM Bot task): SU(2) Wilson action, heatbath (Kennedy-Pendleton) + overrelaxation,
//! on an asymmetric Ls^3 x Lt periodic lattice (dir 0 = time, slowest index).
//! Measurement: SPATIAL (3D, per-timeslice) Wilson gradient flow of the spatial links
//! (Euler / stout-type steps U <- exp(eps * P_su2[A U^dag]) U, A = sum of the 4 spatial
//! staples; flow time t in lattice units, smoothing radius sqrt(6 t)). Because the flow
//! acts within each timeslice, the smoothed operator lives on one timeslice and
//! R(n) = <O(0) O(n)>_c is a genuine transfer-matrix (reflection-positive) correlator.
//! At each requested flow time we record, per timeslice and per spatial plane, the
//! zero-momentum (spatially summed) s x s Wilson loop average (1/2) Tr W.
//! Record layout per measurement (f64 LE):
//!   [plaq4d, then for each level: (E_s = avg spatial plaq, then for each side: 3*Lt values (plane-major: plane*Lt + t))]
//! Checkpoint: gauge field + counters every `ckpt` measurements; --resume continues.
use std::f64::consts::PI;
use std::io::{Read, Write, Seek, SeekFrom};
use std::time::Instant;

type Su2 = [f64; 4];
const ID: Su2 = [1.0, 0.0, 0.0, 0.0];
#[inline] fn mul(a: Su2, b: Su2) -> Su2 { [
    a[0]*b[0]-a[1]*b[1]-a[2]*b[2]-a[3]*b[3],
    a[0]*b[1]+b[0]*a[1]-(a[2]*b[3]-a[3]*b[2]),
    a[0]*b[2]+b[0]*a[2]-(a[3]*b[1]-a[1]*b[3]),
    a[0]*b[3]+b[0]*a[3]-(a[1]*b[2]-a[2]*b[1])] }
#[inline] fn dag(a: Su2) -> Su2 { [a[0], -a[1], -a[2], -a[3]] }
#[inline] fn dot(a: Su2, b: Su2) -> f64 { a[0]*b[0]+a[1]*b[1]+a[2]*b[2]+a[3]*b[3] }
#[inline] fn add(a: Su2, b: Su2) -> Su2 { [a[0]+b[0], a[1]+b[1], a[2]+b[2], a[3]+b[3]] }
#[inline] fn scale(a: Su2, s: f64) -> Su2 { [a[0]*s, a[1]*s, a[2]*s, a[3]*s] }
#[inline] fn renorm(a: Su2) -> Su2 { let n = dot(a,a).sqrt(); if n > 0.0 { scale(a, 1.0/n) } else { ID } }

struct Rng(u64);
impl Rng {
    #[inline] fn next_u64(&mut self) -> u64 { self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15); let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9); z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB); z ^ (z >> 31) }
    #[inline] fn f(&mut self) -> f64 { (self.next_u64() >> 11) as f64 * (1.0 / (1u64 << 53) as f64) }
    #[inline] fn open(&mut self) -> f64 { 1.0 - self.f() }
}
#[inline] fn splitmix(z: u64) -> u64 { let mut r = Rng(z); r.next_u64() }
#[inline] fn stream_seed(g: u64, sw: u64, pass: u64, link: usize) -> u64 {
    let s = splitmix(g ^ sw.wrapping_mul(0xD1B54A32D192ED03)); let s = splitmix(s ^ pass.wrapping_mul(0xA0761D6478BD642F));
    splitmix(s ^ (link as u64).wrapping_mul(0xE7037ED1A0B428DB)) }
fn random_su2(r: &mut Rng) -> Su2 { loop {
    let x1 = 2.0*r.f()-1.0; let y1 = 2.0*r.f()-1.0; let s1 = x1*x1+y1*y1; if s1 >= 1.0 { continue; }
    let x2 = 2.0*r.f()-1.0; let y2 = 2.0*r.f()-1.0; let s2 = x2*x2+y2*y2; if s2 >= 1.0 || s2 == 0.0 { continue; }
    let f = ((1.0-s1)/s2).sqrt(); return [x1, y1, x2*f, y2*f]; } }
fn sample_a0(lambda: f64, r: &mut Rng) -> f64 {
    for _ in 0..1000 { let r1 = r.open(); let r2 = r.f(); let r3 = r.open(); let c = (2.0*PI*r2).cos();
        let d = -(r1.ln() + c*c*r3.ln())/lambda; let r4 = r.f(); if r4*r4 <= 1.0 - 0.5*d { return 1.0 - d; } }
    loop { let a0 = 2.0*r.f()-1.0; if r.f() <= (1.0-a0*a0).sqrt() { return a0; } } }
fn heatbath_link(a: Su2, beta: f64, r: &mut Rng) -> Su2 {
    let k = dot(a,a).sqrt(); if k < 1e-12 { return random_su2(r); }
    let v = scale(a, 1.0/k); let w0 = sample_a0(beta*k, r);
    let rr = (1.0-w0*w0).max(0.0).sqrt(); let ct = 2.0*r.f()-1.0; let ph = 2.0*PI*r.f(); let st = (1.0-ct*ct).max(0.0).sqrt();
    renorm(mul([w0, rr*st*ph.cos(), rr*st*ph.sin(), rr*ct], v)) }
fn overrelax_link(u: Su2, a: Su2) -> Su2 { let k = dot(a,a).sqrt(); if k < 1e-12 { return u; } let v = scale(a, 1.0/k); renorm(mul(mul(v, dag(u)), v)) }

struct Geo { ls: usize, lt: usize, vol: usize, vs: usize, fwd: Vec<u32>, bwd: Vec<u32> }
impl Geo {
    fn new(ls: usize, lt: usize) -> Geo {
        let vs = ls*ls*ls; let vol = vs*lt; let dims = [lt, ls, ls, ls]; let strides = [vs, ls*ls, ls, 1];
        let mut fwd = vec![0u32; vol*4]; let mut bwd = vec![0u32; vol*4];
        for s in 0..vol { for mu in 0..4 { let c = (s / strides[mu]) % dims[mu];
            let f = if c+1 == dims[mu] { s + strides[mu] - dims[mu]*strides[mu] } else { s + strides[mu] };
            let b = if c == 0 { s + (dims[mu]-1)*strides[mu] } else { s - strides[mu] };
            fwd[s*4+mu] = f as u32; bwd[s*4+mu] = b as u32; } }
        Geo { ls, lt, vol, vs, fwd, bwd } }
    #[inline] fn f(&self, s: usize, mu: usize) -> usize { self.fwd[s*4+mu] as usize }
    #[inline] fn b(&self, s: usize, mu: usize) -> usize { self.bwd[s*4+mu] as usize }
    fn parity(&self, s: usize) -> usize { let t = s / self.vs; let r = s % self.vs; let z = r/(self.ls*self.ls); let y = (r/self.ls)%self.ls; let x = r%self.ls; (t+z+y+x)%2 }
}

/// Staple sum A (dot(U,A) = sum of plaquettes containing U) over directions nu in `nus`.
#[inline]
unsafe fn staple(base: *const Su2, g: &Geo, s: usize, mu: usize, nus: &[usize]) -> Su2 {
    let xp = g.f(s, mu); let mut a = [0.0; 4];
    for &nu in nus { if nu == mu { continue; }
        let xn = g.f(s, nu);
        let fw = mul(mul(*base.add(xp*4+nu), dag(*base.add(xn*4+mu))), dag(*base.add(s*4+nu)));
        let xm = g.b(s, nu); let xmp = g.f(xm, mu);
        let bw = mul(mul(dag(*base.add(xmp*4+nu)), dag(*base.add(xm*4+mu))), *base.add(xm*4+nu));
        a = add(a, add(fw, bw)); }
    dag(a) }
const ALL: [usize; 4] = [0,1,2,3];
const SPA: [usize; 3] = [1,2,3];

fn sweep(links: &mut [Su2], g: &Geo, classes: &[Vec<usize>], beta: f64, nor: usize, sw: u64, seed: u64, nth: usize) {
    let base = links.as_mut_ptr() as usize; let barrier = std::sync::Barrier::new(nth);
    std::thread::scope(|sc| { for tid in 0..nth { let barrier = &barrier; sc.spawn(move || {
        let base = base as *mut Su2;
        for pass in 0..(1+nor) { for mu in 0..4 { for par in 0..2 {
            let idx = &classes[mu*2+par]; let n = idx.len(); let ch = (n+nth-1)/nth; let lo = (tid*ch).min(n); let hi = ((tid+1)*ch).min(n);
            let tag = ((pass as u64) << 8) | ((par as u64) << 2) | mu as u64;
            for &li in &idx[lo..hi] { unsafe {
                let a = staple(base, g, li/4, li%4, &ALL);
                let v = if pass == 0 { let mut r = Rng(stream_seed(seed, sw, tag, li)); heatbath_link(a, beta, &mut r) } else { overrelax_link(*base.add(li), a) };
                *base.add(li) = v; } }
            barrier.wait(); } } } }); } }); }

fn plaq4(links: &[Su2], g: &Geo, nth: usize) -> f64 {
    let ch = (g.vol+nth-1)/nth;
    let tot: f64 = std::thread::scope(|sc| { let hs: Vec<_> = (0..nth).map(|t| sc.spawn(move || { let mut s = 0.0;
        for x in (t*ch)..((t+1)*ch).min(g.vol) { for mu in 0..4 { for nu in (mu+1)..4 {
            let p = mul(mul(links[x*4+mu], links[g.f(x,mu)*4+nu]), dag(mul(links[x*4+nu], links[g.f(x,nu)*4+mu]))); s += p[0]; } } } s })).collect();
        hs.into_iter().map(|h| h.join().unwrap()).sum() });
    tot / (6.0 * g.vol as f64) }

/// One Euler step of the spatial (3D) Wilson flow on spatial links: src -> dst (time links copied).
fn flow_step(src: &[Su2], dst: &mut [Su2], g: &Geo, eps: f64, nth: usize) {
    let ch = (g.vol+nth-1)/nth;
    std::thread::scope(|sc| { for (ci, out) in dst.chunks_mut(ch*4).enumerate() { sc.spawn(move || {
        let s0 = ci*ch; let base = src.as_ptr();
        for j in 0..out.len()/4 { let s = s0+j; out[j*4] = src[s*4];
            for mu in 1..4 { let u = src[s*4+mu]; let a = unsafe { staple(base, g, s, mu, &SPA) };
                let w = mul(a, dag(u)); // vector part = generator direction (dV/dt = w_vec V)
                let v = [w[1]*eps, w[2]*eps, w[3]*eps]; let n = (v[0]*v[0]+v[1]*v[1]+v[2]*v[2]).sqrt();
                let e = if n > 1e-15 { let sn = n.sin()/n; [n.cos(), v[0]*sn, v[1]*sn, v[2]*sn] } else { ID };
                out[j*4+mu] = renorm(mul(e, u)); } } }); } }); }

/// Per-timeslice, per-plane zero-momentum averages of (1/2)Tr of s x s spatial loops, for all sides.
/// Returns vec indexed [side_index][plane*lt + t]; plus average spatial plaquette.
fn loops(links: &[Su2], g: &Geo, sides: &[usize], nth: usize) -> (Vec<Vec<f64>>, f64) {
    let smax = *sides.iter().max().unwrap(); let vs = g.vs; let lt = g.lt;
    let per_t: Vec<Vec<f64>> = std::thread::scope(|sc| { let hs: Vec<_> = (0..nth).map(|tid| sc.spawn(move || {
        let mut res: Vec<(usize, Vec<f64>)> = Vec::new();
        let mut line = vec![ID; vs*3];
        let mut t = tid; while t < lt {
            let mut out = vec![0f64; sides.len()*3 + 1];
            for v in line.iter_mut() { *v = ID; }
            let off = t*vs;
            // pos[k][s][d]: site reached from s by k steps in direction d (we carry it implicitly)
            let mut tip: Vec<[u32;3]> = (0..vs).map(|s| [(off+s) as u32; 3]).collect();
            for k in 1..=smax {
                for s in 0..vs { for d in 0..3 { let y = tip[s][d] as usize;
                    line[s*3+d] = mul(line[s*3+d], links[y*4+d+1]); tip[s][d] = g.f(y, d+1) as u32; } }
                if let Some(si) = sides.iter().position(|&q| q == k) {
                    let mut pl = [0f64; 3]; let mut p = 0;
                    for a in 0..3 { for b in (a+1)..3 { let mut acc = 0.0;
                        for s in 0..vs { let xa = tip[s][a] as usize - off; let xb = tip[s][b] as usize - off;
                            let pa = mul(line[s*3+a], line[xa*3+b]); let pb = mul(line[s*3+b], line[xb*3+a]); acc += dot(pa, pb); }
                        pl[p] = acc / vs as f64; p += 1; } }
                    for p in 0..3 { out[si*3+p] = pl[p]; }
                }
                if k == 1 && !sides.contains(&1) { let mut acc = 0.0;
                    for a in 0..3 { for b in (a+1)..3 { for s in 0..vs { let xa = tip[s][a] as usize - off; let xb = tip[s][b] as usize - off;
                        acc += dot(mul(line[s*3+a], line[xa*3+b]), mul(line[s*3+b], line[xb*3+a])); } } }
                    out[sides.len()*3] = acc / (3.0*vs as f64); }
            }
            if let Some(si) = sides.iter().position(|&q| q == 1) { out[sides.len()*3] = (out[si*3]+out[si*3+1]+out[si*3+2])/3.0; }
            res.push((t, out)); t += nth; }
        res })).collect();
        let mut all: Vec<(usize, Vec<f64>)> = hs.into_iter().flat_map(|h| h.join().unwrap()).collect(); all.sort_by_key(|x| x.0); all.into_iter().map(|x| x.1).collect() });
    let mut r = vec![vec![0f64; 3*lt]; sides.len()]; let mut es = 0.0;
    for t in 0..lt { for si in 0..sides.len() { for p in 0..3 { r[si][p*lt+t] = per_t[t][si*3+p]; } } es += per_t[t][sides.len()*3]; }
    (r, es / lt as f64) }

/// One step of LINEAR, UNPROJECTED spatial staple smearing (PLAN option A):
/// V_mu(x) = (1-alpha) U_mu(x) + (alpha/4) * sum of the 4 spatial staples (same orientation as U_mu(x)).
/// No exp, no renormalisation: links become general real quaternions (R_+ x SU(2) or 0). Time links copied.
fn linear_smear_step(src: &[Su2], dst: &mut [Su2], g: &Geo, alpha: f64, nth: usize) {
    let ch = (g.vol+nth-1)/nth;
    std::thread::scope(|sc| { for (ci, out) in dst.chunks_mut(ch*4).enumerate() { sc.spawn(move || {
        let s0 = ci*ch; let base = src.as_ptr();
        for j in 0..out.len()/4 { let s = s0+j; out[j*4] = src[s*4];
            for mu in 1..4 { let a = unsafe { staple(base, g, s, mu, &SPA) };
                out[j*4+mu] = add(scale(src[s*4+mu], 1.0-alpha), scale(a, alpha/4.0)); } } }); } }); }

/// Spatial Polyakov loops (product of Ls links along spatial direction d) on the given (smoothed) links.
/// Returns [mean_lines P_x, P_y, P_z, mean_lines P_x^2, P_y^2, P_z^2] with P = (1/2)Tr = scalar part.
fn spatial_poly(links: &[Su2], g: &Geo, nth: usize) -> [f64; 6] {
    let strides = [g.vs, g.ls*g.ls, g.ls, 1]; let ls = g.ls;
    let mut out = [0f64; 6];
    for d in 1..4 {
        let starts: Vec<usize> = (0..g.vol).filter(|&s| (s / strides[d]) % ls == 0).collect();
        let ch = (starts.len()+nth-1)/nth;
        let (s1, s2): (f64, f64) = std::thread::scope(|sc| { let hs: Vec<_> = starts.chunks(ch).map(|c| sc.spawn(move || {
            let (mut a, mut b) = (0.0, 0.0);
            for &s0 in c { let mut p = ID; let mut y = s0; for _ in 0..ls { p = mul(p, links[y*4+d]); y = g.f(y, d); } a += p[0]; b += p[0]*p[0]; }
            (a, b) })).collect();
            hs.into_iter().map(|h| h.join().unwrap()).fold((0.0, 0.0), |x, y| (x.0+y.0, x.1+y.1)) });
        out[d-1] = s1 / starts.len() as f64; out[d+2] = s2 / starts.len() as f64; }
    out }

/// Save configuration as f32 (16-byte header: sweep, nmeas as u64 LE), atomic rename.
fn save_cfg_f32(path: &str, links: &[Su2], sw: u64, nmeas: u64) {
    let tmp = format!("{path}.tmp"); let mut f = std::io::BufWriter::new(std::fs::File::create(&tmp).unwrap());
    f.write_all(&sw.to_le_bytes()).unwrap(); f.write_all(&nmeas.to_le_bytes()).unwrap();
    let mut buf = Vec::with_capacity(links.len()*16); for l in links { for c in l { buf.extend_from_slice(&(*c as f32).to_le_bytes()); } }
    f.write_all(&buf).unwrap(); let f = f.into_inner().unwrap(); f.sync_all().unwrap(); std::fs::rename(&tmp, path).unwrap(); }

/// Threads override: if a threads file is given, re-read it (clamped to 1..=max) before every sweep / measurement step.
fn read_threads(path: &Option<String>, cur: usize, max: usize) -> usize {
    match path { None => cur, Some(p) => match std::fs::read_to_string(p) { Ok(s) => match s.trim().parse::<usize>() { Ok(n) if n >= 1 => n.min(max), _ => cur }, Err(_) => cur } } }

fn save_ckpt(path: &str, links: &[Su2], sw: u64, nmeas: u64) {
    let tmp = format!("{path}.tmp"); let mut f = std::fs::File::create(&tmp).unwrap();
    f.write_all(&sw.to_le_bytes()).unwrap(); f.write_all(&nmeas.to_le_bytes()).unwrap();
    let mut buf = Vec::with_capacity(links.len()*32); for l in links { for c in l { buf.extend_from_slice(&c.to_le_bytes()); } }
    f.write_all(&buf).unwrap(); f.sync_all().unwrap(); std::fs::rename(&tmp, path).unwrap(); }
fn load_ckpt(path: &str, n: usize) -> Option<(Vec<Su2>, u64, u64)> {
    let mut f = std::fs::File::open(path).ok()?; let mut b = Vec::new(); f.read_to_end(&mut b).ok()?;
    if b.len() != 16 + n*32 { return None; }
    let sw = u64::from_le_bytes(b[0..8].try_into().unwrap()); let nm = u64::from_le_bytes(b[8..16].try_into().unwrap());
    let links = (0..n).map(|i| { let o = 16 + i*32; [0,1,2,3].map(|c| f64::from_le_bytes(b[o+8*c..o+8*c+8].try_into().unwrap())) }).collect();
    Some((links, sw, nm)) }


// ---------------------------------------------------------------------------------------------
// Self-test (P7 f-i): loops() on linearly smeared links == explicit positive combination of
// unsmoothed closed Wilson loops, by brute-force enumeration of the multilinear expansion.
type Path = Vec<(usize, usize, bool)>; // (site, dir, daggered)
fn path_eval(links: &[Su2], p: &Path) -> Su2 { let mut r = ID; for &(s, d, dg) in p { let u = links[s*4+d]; r = mul(r, if dg { dag(u) } else { u }); } r }
fn path_dag(p: &Path) -> Path { p.iter().rev().map(|&(s, d, dg)| (s, d, !dg)).collect() }
/// One linear step of link (y,d) expanded into 5 weighted paths of the input links.
fn expand1(g: &Geo, y: usize, d: usize, alpha: f64) -> Vec<(f64, Path)> {
    let mut v = vec![(1.0-alpha, vec![(y, d, false)])];
    for &nu in &SPA { if nu == d { continue; }
        v.push((alpha/4.0, vec![(y, nu, false), (g.f(y, nu), d, false), (g.f(y, d), nu, true)]));
        let ym = g.b(y, nu); v.push((alpha/4.0, vec![(ym, nu, true), (ym, d, false), (g.f(ym, d), nu, false)])); }
    v }
/// n linear steps of link (y,d) expanded recursively into weighted unsmoothed paths.
fn expand_n(g: &Geo, y: usize, d: usize, alpha: f64, n: usize) -> Vec<(f64, Path)> {
    if n == 0 { return vec![(1.0, vec![(y, d, false)])]; }
    let mut out = Vec::new();
    for (w, p) in expand1(g, y, d, alpha) {
        // each factor of p is a level-(n-1) smeared link (possibly daggered): expand and take the cartesian product
        let mut acc: Vec<(f64, Path)> = vec![(w, vec![])];
        for &(s, dd, dg) in &p { let sub = expand_n(g, s, dd, alpha, n-1);
            let sub: Vec<(f64, Path)> = if dg { sub.iter().map(|(w, q)| (*w, path_dag(q))).collect() } else { sub };
            let mut nacc = Vec::with_capacity(acc.len()*sub.len());
            for (wa, pa) in &acc { for (wb, pb) in &sub { let mut q = pa.clone(); q.extend_from_slice(pb); nacc.push((wa*wb, q)); } }
            acc = nacc; }
        out.extend(acc); }
    out }
fn selftest_linear() {
    let (ls, lt) = (4usize, 4usize); let g = Geo::new(ls, lt); let mut r = Rng(0xC0FFEE);
    let links: Vec<Su2> = (0..g.vol*4).map(|_| random_su2(&mut r)).collect(); // hot (random) config: strongest test
    let alpha = 0.37;
    let mut v1 = links.clone(); linear_smear_step(&links, &mut v1, &g, alpha, 2);
    let mut v2 = v1.clone(); linear_smear_step(&v1, &mut v2, &g, alpha, 2);
    // (A) link level, n = 1, 2, 3 steps: V_n(y,d) vs sum of weighted unsmoothed paths
    // (n=3 would be 5+4*505^3 ~ 5e8 terms/link: infeasible; n=1,2 by full enumeration)
    let mut maxres = [0f64; 2]; let mut nterms = [0usize; 2]; let mut minw = [f64::INFINITY; 2];
    for (k, vn) in [&v1, &v2].iter().enumerate() {
        let sites: Vec<usize> = (0..g.vol).collect();
        for &y in &sites { for d in 1..4 {
            let ex = expand_n(&g, y, d, alpha, k+1); nterms[k] = ex.len();
            let mut sum = [0.0; 4]; for (w, p) in &ex { sum = add(sum, scale(path_eval(&links, p), *w)); minw[k] = minw[k].min(*w); }
            let v = vn[y*4+d]; for c in 0..4 { maxres[k] = maxres[k].max((sum[c]-v[c]).abs()); } } }
        // time links unchanged
        for y in 0..g.vol { for c in 0..4 { maxres[k] = maxres[k].max((vn[y*4][c]-links[y*4][c]).abs()); } } }
    for k in 0..2 { println!("link-level n={}: terms/link={} min weight={:.3e} (all >0) max|V - sum w*path| = {:.3e}", k+1, nterms[k], minw[k], maxres[k]); }
    // (B) loops() on V1 vs brute-force enumeration of all products of expanded links (each term = (1/2)Tr of an unsmoothed closed loop)
    let sides = [1usize, 2]; let (rl, _) = loops(&v1, &g, &sides, 2);
    let mut maxd = 0f64; let mut nloopterms = 0usize; let mut neg = 0usize;
    for (si, &k) in sides.iter().enumerate() {
        let tmax = if k == 1 { lt } else { 1 };
        let mut p = 0; for a in 0..3 { for b in (a+1)..3 { let (da, db) = (a+1, b+1);
            for t in 0..tmax { let mut acc = 0.0;
                for s3 in 0..g.vs { let s = t*g.vs + s3;
                    // pa: k links along da from s, then k along db; pb: k along db from s, then k along da.  value = dot(prod pa, prod pb)
                    let mut la: Vec<(usize, usize)> = vec![]; let mut y = s; for _ in 0..k { la.push((y, da)); y = g.f(y, da); } for _ in 0..k { la.push((y, db)); y = g.f(y, db); }
                    let mut lb: Vec<(usize, usize)> = vec![]; let mut y = s; for _ in 0..k { lb.push((y, db)); y = g.f(y, db); } for _ in 0..k { lb.push((y, da)); y = g.f(y, da); }
                    let ea: Vec<Vec<(f64, Su2)>> = la.iter().map(|&(y, d)| expand1(&g, y, d, alpha).into_iter().map(|(w, q)| (w, path_eval(&links, &q))).collect()).collect();
                    let eb: Vec<Vec<(f64, Su2)>> = lb.iter().map(|&(y, d)| expand1(&g, y, d, alpha).into_iter().map(|(w, q)| (w, path_eval(&links, &q))).collect()).collect();
                    let all: Vec<&Vec<(f64, Su2)>> = ea.iter().chain(eb.iter()).collect(); let nl = all.len(); let ntot = 5usize.pow(nl as u32);
                    let mut val = 0.0;
                    for code in 0..ntot { let mut c = code; let mut w = 1.0; let mut pa = ID; let mut pb = ID;
                        for (i, e) in all.iter().enumerate() { let (wi, qi) = e[c % 5]; c /= 5; w *= wi; if i < nl/2 { pa = mul(pa, qi); } else { pb = mul(pb, qi); } }
                        if w <= 0.0 { neg += 1; } val += w * dot(pa, pb); nloopterms += 1; }
                    acc += val; }
                let bf = acc / g.vs as f64; let code = rl[si][p*lt + t]; maxd = maxd.max((bf-code).abs());
                if t == 0 { println!("side {k} plane {p} t=0: loops()={code:.15e} brute-force={bf:.15e} diff={:.2e}", (bf-code).abs()); } }
            p += 1; } } }
    println!("loops() vs brute-force closed-loop expansion: max |diff| = {maxd:.3e} over {nloopterms} explicit unsmoothed-loop terms; non-positive weights: {neg}");
    let ok = maxd < 1e-12 && maxres.iter().all(|&x| x < 1e-12) && neg == 0;
    println!("SELFTEST {}", if ok { "PASS" } else { "FAIL" });
}

fn main() {
    let mut ls = 8usize; let mut lt = 8usize; let mut beta: f64 = 2.5; let mut therm = 200usize; let mut meas = 100usize;
    let mut interval = 2usize; let mut nor = 4usize; let mut sides = vec![2usize]; let mut tflow: Vec<f64> = vec![0.0];
    let mut eps: f64 = 0.05; let mut seed = 1u64; let mut nth = 4usize; let mut out = String::from("out"); let mut ckpt = 25usize; let mut resume = false;
    let mut plaq_only = false; let mut eps2: f64 = 0.1; let mut tswitch: f64 = 0.5; let mut eps3: f64 = 0.1; let mut tswitch2: f64 = 1e9;
    let mut lin_alpha: f64 = 0.5; let mut lin_steps: Vec<usize> = vec![]; let mut thfile: Option<String> = None;
    let mut save_every = 0usize; let mut save_dir = String::new(); let mut therm_ckpt = 100usize;
    let a: Vec<String> = std::env::args().collect(); let mut i = 1;
    while i < a.len() { let k = a[i].as_str(); if k == "--resume" { resume = true; i += 1; continue; } if k == "--plaq-only" { plaq_only = true; i += 1; continue; }
        if k == "--selftest-linear" { selftest_linear(); return; }
        let v = a[i+1].clone(); i += 2;
        match k { "--Ls" => ls = v.parse().unwrap(), "--Lt" => lt = v.parse().unwrap(), "--beta" => beta = v.parse().unwrap(),
            "--therm" => therm = v.parse().unwrap(), "--meas" => meas = v.parse().unwrap(), "--interval" => interval = v.parse().unwrap(),
            "--overrelax" => nor = v.parse().unwrap(), "--sides" => sides = v.split(',').map(|s| s.parse().unwrap()).collect(),
            "--tflow" => tflow = v.split(',').map(|s| s.parse().unwrap()).collect(), "--eps" => eps = v.parse().unwrap(),
            "--seed" => seed = v.parse().unwrap(), "--threads" => nth = v.parse().unwrap(), "--out" => out = v,
            "--ckpt" => ckpt = v.parse().unwrap(), "--eps2" => eps2 = v.parse().unwrap(), "--tswitch" => tswitch = v.parse().unwrap(), "--eps3" => eps3 = v.parse().unwrap(), "--tswitch2" => tswitch2 = v.parse().unwrap(),
            "--linear-alpha" => lin_alpha = v.parse().unwrap(), "--linear-steps" => lin_steps = v.split(',').map(|s| s.parse().unwrap()).collect(),
            "--threads-file" => thfile = Some(v), "--save-every" => save_every = v.parse().unwrap(), "--save-dir" => save_dir = v, "--therm-ckpt" => therm_ckpt = v.parse().unwrap(),
            o => panic!("unknown arg {o}") } }
    assert!(ls % 2 == 0 && lt % 2 == 0);
    tflow.sort_by(|x, y| x.partial_cmp(y).unwrap()); lin_steps.sort();
    let nmax = nth; // threads file may lower (or restore up to) the launch thread count
    let g = Geo::new(ls, lt);
    let mut classes = vec![Vec::new(); 8]; for s in 0..g.vol { let p = g.parity(s); for mu in 0..4 { classes[mu*2+p].push(s*4+mu); } }
    let ckpath = format!("{out}.ckpt"); let datpath = format!("{out}.bin");
    let nlev = tflow.len() + lin_steps.len();
    let hdr = format!("{{\"Ls\":{ls},\"Lt\":{lt},\"beta\":{beta},\"sides\":{:?},\"tflow\":{:?},\"eps\":{eps},\"eps2\":{eps2},\"tswitch\":{tswitch},\"eps3\":{eps3},\"tswitch2\":{tswitch2},\"interval\":{interval},\"overrelax\":{nor},\"seed\":{seed},\"therm\":{therm},\"linear_alpha\":{lin_alpha},\"linear_steps\":{:?},\"poly\":6,\"save_every\":{save_every}}}\n", sides, tflow, lin_steps);
    let t0 = Instant::now();
    let (mut links, mut sw, mut done) = if resume { match load_ckpt(&ckpath, g.vol*4) { Some(x) => { eprintln!("resumed sw={} nmeas={}", x.1, x.2); x } None => panic!("no ckpt") } }
        else { let mut r = Rng(splitmix(seed ^ 0x5151)); ((0..g.vol*4).map(|_| random_su2(&mut r)).collect(), 0u64, 0u64) };
    let therm_from = if !resume { Some(0usize) } else if done == 0 && (sw as usize) < therm { Some(sw as usize) } else { None };
    if let Some(k0) = therm_from {
        for k in k0..therm {
            let n2 = read_threads(&thfile, nth, nmax); if n2 != nth { eprintln!("threads {nth} -> {n2} at therm sweep {k}"); nth = n2; }
            sweep(&mut links, &g, &classes, beta, nor, sw, seed, nth); sw += 1;
            if k % 50 == 0 { eprintln!("therm {k} {:.1}s plaq={:.6} th={nth}", t0.elapsed().as_secs_f64(), plaq4(&links, &g, nth)); }
            if therm_ckpt > 0 && (k+1) % therm_ckpt == 0 && k+1 < therm { save_ckpt(&ckpath, &links, sw, 0); } }
        eprintln!("therm done {:.1}s plaq={:.6}", t0.elapsed().as_secs_f64(), plaq4(&links, &g, nth));
        let mut f = std::fs::File::create(&datpath).unwrap(); f.write_all(hdr.as_bytes()).unwrap();
        save_ckpt(&ckpath, &links, sw, 0); done = 0;
    }
    let reclen = if plaq_only { 1 } else { 1 + nlev*(1 + sides.len()*3*lt) + nlev*6 };
    let mut f = std::fs::OpenOptions::new().read(true).write(true).open(&datpath).unwrap();
    let hlen = { let mut b = Vec::new(); f.read_to_end(&mut b).unwrap(); b.iter().position(|&c| c == b'\n').unwrap() + 1 };
    f.set_len((hlen + done as usize * reclen * 8) as u64).unwrap(); f.seek(SeekFrom::End(0)).unwrap();
    if save_every > 0 { std::fs::create_dir_all(&save_dir).unwrap(); }
    let mut fa = links.clone(); let mut fb = links.clone();
    let tm = Instant::now(); let mut since = 0usize; let done0 = done;
    let smain = sides[sides.len()/2]; let simain = sides.len()/2;
    while (done as usize) < meas {
        for _ in 0..interval { let n2 = read_threads(&thfile, nth, nmax); if n2 != nth { eprintln!("threads {nth} -> {n2} at meas {done}"); nth = n2; }
            sweep(&mut links, &g, &classes, beta, nor, sw, seed, nth); sw += 1; }
        let mut rec = vec![plaq4(&links, &g, nth)];
        let mut obar: Vec<f64> = vec![]; let mut polys: Vec<[f64; 6]> = vec![];
        if !plaq_only {
            fa.copy_from_slice(&links); let mut tcur = 0.0;
            for &tf in &tflow {
                while tcur < tf - 1e-9 { let h = (if tcur < tswitch - 1e-9 { eps.min(tswitch - tcur) } else if tcur < tswitch2 - 1e-9 { eps2.min(tswitch2 - tcur) } else { eps3 }).min(tf - tcur); flow_step(&fa, &mut fb, &g, h, nth); std::mem::swap(&mut fa, &mut fb); tcur += h; }
                let (r, es) = loops(&fa, &g, &sides, nth); obar.push(r[simain].iter().sum::<f64>() / (3*lt) as f64); rec.push(es); for v in r { rec.extend(v); }
                polys.push(spatial_poly(&fa, &g, nth));
            }
            fa.copy_from_slice(&links); let mut ncur = 0usize;
            for &nl in &lin_steps {
                while ncur < nl { linear_smear_step(&fa, &mut fb, &g, lin_alpha, nth); std::mem::swap(&mut fa, &mut fb); ncur += 1; }
                let (r, es) = loops(&fa, &g, &sides, nth); obar.push(r[simain].iter().sum::<f64>() / (3*lt) as f64); rec.push(es); for v in r { rec.extend(v); }
                polys.push(spatial_poly(&fa, &g, nth));
            }
            for p in &polys { rec.extend_from_slice(p); }
        }
        let bytes: Vec<u8> = rec.iter().flat_map(|x| x.to_le_bytes()).collect(); f.write_all(&bytes).unwrap();
        done += 1; since += 1;
        if save_every > 0 && done as usize % save_every == 0 { save_cfg_f32(&format!("{save_dir}/cfg_{done:05}.f32"), &links, sw, done); }
        if since >= ckpt || done as usize == meas { f.sync_all().unwrap(); save_ckpt(&ckpath, &links, sw, done); since = 0; }
        let pl = polys.last().map(|p| format!("[{:+.4},{:+.4},{:+.4}]", p[0], p[1], p[2])).unwrap_or_default();
        eprintln!("meas {done}/{meas} {:.1}s ({:.2}s/meas) plaq={:.6} th={nth} O_s{smain}={} P_last={pl}", t0.elapsed().as_secs_f64(), tm.elapsed().as_secs_f64()/((done-done0) as f64).max(1.0), rec[0],
            obar.iter().map(|x| format!("{x:.5}")).collect::<Vec<_>>().join(","));
    }
    eprintln!("done {:.1}s", t0.elapsed().as_secs_f64());
}
