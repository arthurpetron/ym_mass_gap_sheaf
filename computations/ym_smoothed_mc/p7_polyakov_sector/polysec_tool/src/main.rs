//! polysec: single-thread spatial-Polyakov (torelon) correlator tool for P7 SU(2) configs.
//! MC only, not proof.
//! Layout (same as P4/P7): dirs [0=t,1,2,3], strides [vs, ls^2, ls, 1], links[site*4+mu], SU(2) quaternion.
//! Mode A  measure: read f32 cfgs (16-byte header), per timeslice APE-smear spatial links (projected),
//!         record zero-momentum P_d(t) = mean over ls^2 lines of (1/2)Tr prod_{ls} V_d, d=1..3, at levels.
//! Mode B  generate: load f64 ckpt (16-byte header), run heatbath+OR sweeps (1 thread), measure every
//!         `interval` sweeps as in mode A (no cfg saving).
//! Output: header JSON line, then per measurement f64 LE: [plaq4d, for lev: for d in 0..3: P_d(t) t=0..lt-1].
use std::f64::consts::PI;
use std::io::{Read, Write};
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
fn geo(dims: [usize; 4]) -> (Vec<u32>, Vec<u32>) {
    let vol: usize = dims.iter().product(); let strides = [dims[1]*dims[2]*dims[3], dims[2]*dims[3], dims[3], 1];
    let mut fwd = vec![0u32; vol*4]; let mut bwd = vec![0u32; vol*4];
    for s in 0..vol { for mu in 0..4 { let c = (s / strides[mu]) % dims[mu];
        let f = if c+1 == dims[mu] { s + strides[mu] - dims[mu]*strides[mu] } else { s + strides[mu] };
        let b = if c == 0 { s + (dims[mu]-1)*strides[mu] } else { s - strides[mu] };
        fwd[s*4+mu] = f as u32; bwd[s*4+mu] = b as u32; } }
    (fwd, bwd) }
impl Geo { fn new(ls: usize, lt: usize) -> Geo { let (fwd, bwd) = geo([lt, ls, ls, ls]); Geo { ls, lt, vol: ls*ls*ls*lt, vs: ls*ls*ls, fwd, bwd } }
    #[inline] fn f(&self, s: usize, mu: usize) -> usize { self.fwd[s*4+mu] as usize }
    #[inline] fn b(&self, s: usize, mu: usize) -> usize { self.bwd[s*4+mu] as usize } }

/// staple oriented like U_mu(s): sum_nu U_nu(s) U_mu(s+nu) U_nu(s+mu)^dag + backward. Generic over neighbour tables.
#[inline] fn staple(l: &[Su2], fw: &[u32], bw: &[u32], s: usize, mu: usize, nus: &[usize]) -> Su2 {
    let f = |x: usize, m: usize| fw[x*4+m] as usize; let b = |x: usize, m: usize| bw[x*4+m] as usize;
    let xp = f(s, mu); let mut a = [0.0; 4];
    for &nu in nus { if nu == mu { continue; }
        let xn = f(s, nu);
        let fwv = mul(mul(l[xp*4+nu], dag(l[xn*4+mu])), dag(l[s*4+nu]));
        let xm = b(s, nu); let xmp = f(xm, mu);
        let bwv = mul(mul(dag(l[xmp*4+nu]), dag(l[xm*4+mu])), l[xm*4+nu]);
        a = add(a, add(fwv, bwv)); }
    dag(a) }
const ALL: [usize; 4] = [0,1,2,3]; const SPA: [usize; 3] = [1,2,3];

fn sweep(l: &mut [Su2], g: &Geo, classes: &[Vec<usize>], beta: f64, nor: usize, r: &mut Rng) {
    for pass in 0..(1+nor) { for mu in 0..4 { for par in 0..2 { for &li in &classes[mu*2+par] {
        let a = staple(l, &g.fwd, &g.bwd, li/4, li%4, &ALL);
        l[li] = if pass == 0 { heatbath_link(a, beta, r) } else { overrelax_link(l[li], a) }; } } } } }
fn plaq4(l: &[Su2], g: &Geo) -> f64 { let mut s = 0.0;
    for x in 0..g.vol { for mu in 0..4 { for nu in (mu+1)..4 {
        s += mul(mul(l[x*4+mu], l[g.f(x,mu)*4+nu]), dag(mul(l[x*4+nu], l[g.f(x,nu)*4+mu])))[0]; } } }
    s / (6.0*g.vol as f64) }

/// Slice-local work: links of one timeslice (vs*4, index r*4+mu with r local), 3D neighbour tables
/// (slot 0 unused; mu=1..3 identical to 4D within slice).
struct Slice { ls: usize, vs: usize, fwd: Vec<u32>, bwd: Vec<u32> }
impl Slice { fn new(ls: usize) -> Slice { let (fwd, bwd) = geo([1, ls, ls, ls]); Slice { ls, vs: ls*ls*ls, fwd, bwd } } }
fn ape_step(src: &[Su2], dst: &mut [Su2], sl: &Slice, alpha: f64) {
    for r in 0..sl.vs { dst[r*4] = src[r*4];
        for mu in 1..4 { let a = staple(src, &sl.fwd, &sl.bwd, r, mu, &SPA);
            dst[r*4+mu] = renorm(add(scale(src[r*4+mu], 1.0-alpha), scale(a, alpha/4.0))); } } }
fn poly_slice(l: &[Su2], sl: &Slice) -> [f64; 3] {
    let strides = [0, sl.ls*sl.ls, sl.ls, 1]; let mut out = [0f64; 3];
    for d in 1..4 { let mut acc = 0.0; let mut n = 0usize;
        for r0 in 0..sl.vs { if (r0 / strides[d]) % sl.ls != 0 { continue; }
            let mut p = ID; let mut y = r0; for _ in 0..sl.ls { p = mul(p, l[y*4+d]); y = sl.fwd[y*4+d] as usize; }
            acc += p[0]; n += 1; }
        out[d-1] = acc / n as f64; }
    out }
/// Measure one configuration: returns per level [d][t].
fn measure(l: &[Su2], g: &Geo, sl: &Slice, levels: &[usize], alpha: f64) -> Vec<f64> {
    let nl = levels.len(); let mut out = vec![0f64; nl*3*g.lt];
    let mut a = vec![ID; sl.vs*4]; let mut b = vec![ID; sl.vs*4];
    for t in 0..g.lt { a.copy_from_slice(&l[t*g.vs*4..(t+1)*g.vs*4]); let mut cur = 0usize;
        for (li, &n) in levels.iter().enumerate() {
            while cur < n { ape_step(&a, &mut b, sl, alpha); std::mem::swap(&mut a, &mut b); cur += 1; }
            let p = poly_slice(&a, sl); for d in 0..3 { out[(li*3+d)*g.lt + t] = p[d]; } } }
    out }
/// Streaming measure from an f32 cfg file: one timeslice in RAM at a time (low memory).
/// Returns (mean unsmeared spatial plaquette, per-level [d][t]).
fn measure_stream(path: &str, g: &Geo, sl: &Slice, levels: &[usize], alpha: f64) -> (f64, Vec<f64>) {
    use std::io::{Seek, SeekFrom};
    let mut fh = std::fs::File::open(path).unwrap();
    assert_eq!(fh.metadata().unwrap().len() as usize, 16 + g.vol*4*16, "{path}: size");
    let nl = levels.len(); let mut out = vec![0f64; nl*3*g.lt]; let mut es = 0.0;
    let mut buf = vec![0u8; g.vs*4*16]; let mut a = vec![ID; sl.vs*4]; let mut b = vec![ID; sl.vs*4];
    for t in 0..g.lt { fh.seek(SeekFrom::Start((16 + t*g.vs*4*16) as u64)).unwrap(); fh.read_exact(&mut buf).unwrap();
        for i in 0..sl.vs*4 { let o = i*16; a[i] = renorm([0,1,2,3].map(|c| f32::from_le_bytes(buf[o+4*c..o+4*c+4].try_into().unwrap()) as f64)); }
        let mut acc = 0.0; for r in 0..sl.vs { for mu in 1..4 { acc += dot(a[r*4+mu], staple(&a, &sl.fwd, &sl.bwd, r, mu, &SPA)); } }
        es += acc / (12.0 * sl.vs as f64);
        let mut cur = 0usize;
        for (li, &n) in levels.iter().enumerate() {
            while cur < n { ape_step(&a, &mut b, sl, alpha); std::mem::swap(&mut a, &mut b); cur += 1; }
            let p = poly_slice(&a, sl); for d in 0..3 { out[(li*3+d)*g.lt + t] = p[d]; } } }
    (es / g.lt as f64, out) }
#[allow(dead_code)]
fn read_f32_cfg(path: &str, n: usize) -> Vec<Su2> {
    let mut f = std::fs::File::open(path).unwrap(); let mut b = Vec::new(); f.read_to_end(&mut b).unwrap();
    assert_eq!(b.len(), 16 + n*16, "{path}: size");
    (0..n).map(|i| { let o = 16 + i*16; renorm([0,1,2,3].map(|c| f32::from_le_bytes(b[o+4*c..o+4*c+4].try_into().unwrap()) as f64)) }).collect() }
fn read_f64_ckpt(path: &str, n: usize) -> Vec<Su2> {
    let mut f = std::fs::File::open(path).unwrap(); let mut b = Vec::new(); f.read_to_end(&mut b).unwrap();
    assert_eq!(b.len(), 16 + n*32, "{path}: size");
    (0..n).map(|i| { let o = 16 + i*32; [0,1,2,3].map(|c| f64::from_le_bytes(b[o+8*c..o+8*c+8].try_into().unwrap())) }).collect() }

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let mut mode = String::new(); let mut ls = 48usize; let mut lt = 48usize; let mut beta = 2.95f64;
    let mut levels: Vec<usize> = vec![0, 5, 10, 20]; let mut alpha = 0.5f64; let mut out = String::from("poly.bin");
    let mut cfgs: Vec<String> = vec![]; let mut ckpt = String::new(); let mut nmeas = 0usize; let mut interval = 4usize;
    let mut nor = 4usize; let mut seed = 1u64; let mut i = 1;
    while i < a.len() { let k = a[i].as_str(); let v = a[i+1].clone(); i += 2;
        match k { "--mode" => mode = v, "--Ls" => ls = v.parse().unwrap(), "--Lt" => lt = v.parse().unwrap(), "--beta" => beta = v.parse().unwrap(),
            "--levels" => levels = v.split(',').map(|s| s.parse().unwrap()).collect(), "--alpha" => alpha = v.parse().unwrap(),
            "--out" => out = v, "--cfglist" => cfgs = std::fs::read_to_string(&v).unwrap().lines().map(|s| s.trim().to_string()).filter(|s| !s.is_empty()).collect(),
            "--ckpt" => ckpt = v, "--meas" => nmeas = v.parse().unwrap(), "--interval" => interval = v.parse().unwrap(),
            "--overrelax" => nor = v.parse().unwrap(), "--seed" => seed = v.parse().unwrap(), o => panic!("unknown {o}") } }
    let g = Geo::new(ls, lt); let sl = Slice::new(ls); let t0 = Instant::now();
    let hdr = format!("{{\"mode\":\"{mode}\",\"Ls\":{ls},\"Lt\":{lt},\"beta\":{beta},\"levels\":{:?},\"alpha\":{alpha},\"interval\":{interval},\"overrelax\":{nor},\"seed\":{seed},\"ncfg\":{},\"rec\":\"plaq4, lev x d(3) x t\"}}\n", levels, if mode == "measure" { cfgs.len() } else { nmeas });
    let mut f = std::fs::File::create(&out).unwrap(); f.write_all(hdr.as_bytes()).unwrap();
    let emit = |f: &mut std::fs::File, plaq: f64, m: &[f64]| { let mut rec = vec![plaq]; rec.extend_from_slice(m);
        let by: Vec<u8> = rec.iter().flat_map(|x| x.to_le_bytes()).collect(); f.write_all(&by).unwrap(); f.flush().unwrap(); };
    if mode == "measure" {
        for (k, c) in cfgs.iter().enumerate() { let (p, m) = measure_stream(c, &g, &sl, &levels, alpha); emit(&mut f, p, &m);
            let last = levels.len()-1; let pl: Vec<f64> = (0..3).map(|d| m[(last*3+d)*lt..(last*3+d+1)*lt].iter().sum::<f64>()/lt as f64).collect();
            eprintln!("cfg {}/{} {c} {:.1}s plaq={p:.6} P_lastlev=[{:+.4},{:+.4},{:+.4}]", k+1, cfgs.len(), t0.elapsed().as_secs_f64(), pl[0], pl[1], pl[2]); }
    } else if mode == "generate" {
        let mut l = read_f64_ckpt(&ckpt, g.vol*4); let mut r = Rng(seed ^ 0x9E37_79B9_7F4A_7C15);
        let mut classes = vec![Vec::new(); 8];
        for s in 0..g.vol { let t = s / g.vs; let q = s % g.vs; let z = q/(ls*ls); let y = (q/ls)%ls; let x = q%ls; let p = (t+z+y+x)%2; for mu in 0..4 { classes[mu*2+p].push(s*4+mu); } }
        eprintln!("loaded ckpt plaq={:.6}", plaq4(&l, &g));
        for k in 0..nmeas { for _ in 0..interval { sweep(&mut l, &g, &classes, beta, nor, &mut r); }
            let p = plaq4(&l, &g); let m = measure(&l, &g, &sl, &levels, alpha); emit(&mut f, p, &m);
            let last = levels.len()-1; let pl: Vec<f64> = (0..3).map(|d| m[(last*3+d)*lt..(last*3+d+1)*lt].iter().sum::<f64>()/lt as f64).collect();
            eprintln!("meas {}/{nmeas} {:.1}s plaq={p:.6} P_lastlev=[{:+.4},{:+.4},{:+.4}]", k+1, t0.elapsed().as_secs_f64(), pl[0], pl[1], pl[2]); }
    } else { panic!("--mode measure|generate"); }
    eprintln!("done {:.1}s", t0.elapsed().as_secs_f64());
}
