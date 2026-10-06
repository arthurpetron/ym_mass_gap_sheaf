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

fn main() {
    let mut ls = 8usize; let mut lt = 8usize; let mut beta: f64 = 2.5; let mut therm = 200usize; let mut meas = 100usize;
    let mut interval = 2usize; let mut nor = 4usize; let mut sides = vec![2usize]; let mut tflow: Vec<f64> = vec![0.0];
    let mut eps: f64 = 0.05; let mut seed = 1u64; let mut nth = 4usize; let mut out = String::from("out"); let mut ckpt = 25usize; let mut resume = false;
    let mut plaq_only = false; let mut eps2: f64 = 0.1; let mut tswitch: f64 = 0.5; let mut eps3: f64 = 0.1; let mut tswitch2: f64 = 1e9;
    let a: Vec<String> = std::env::args().collect(); let mut i = 1;
    while i < a.len() { let k = a[i].as_str(); if k == "--resume" { resume = true; i += 1; continue; } if k == "--plaq-only" { plaq_only = true; i += 1; continue; }
        let v = a[i+1].clone(); i += 2;
        match k { "--Ls" => ls = v.parse().unwrap(), "--Lt" => lt = v.parse().unwrap(), "--beta" => beta = v.parse().unwrap(),
            "--therm" => therm = v.parse().unwrap(), "--meas" => meas = v.parse().unwrap(), "--interval" => interval = v.parse().unwrap(),
            "--overrelax" => nor = v.parse().unwrap(), "--sides" => sides = v.split(',').map(|s| s.parse().unwrap()).collect(),
            "--tflow" => tflow = v.split(',').map(|s| s.parse().unwrap()).collect(), "--eps" => eps = v.parse().unwrap(),
            "--seed" => seed = v.parse().unwrap(), "--threads" => nth = v.parse().unwrap(), "--out" => out = v,
            "--ckpt" => ckpt = v.parse().unwrap(), "--eps2" => eps2 = v.parse().unwrap(), "--tswitch" => tswitch = v.parse().unwrap(), "--eps3" => eps3 = v.parse().unwrap(), "--tswitch2" => tswitch2 = v.parse().unwrap(), o => panic!("unknown arg {o}") } }
    assert!(ls % 2 == 0 && lt % 2 == 0);
    tflow.sort_by(|x, y| x.partial_cmp(y).unwrap());
    let g = Geo::new(ls, lt);
    let mut classes = vec![Vec::new(); 8]; for s in 0..g.vol { let p = g.parity(s); for mu in 0..4 { classes[mu*2+p].push(s*4+mu); } }
    let ckpath = format!("{out}.ckpt"); let datpath = format!("{out}.bin");
    let hdr = format!("{{\"Ls\":{ls},\"Lt\":{lt},\"beta\":{beta},\"sides\":{:?},\"tflow\":{:?},\"eps\":{eps},\"eps2\":{eps2},\"tswitch\":{tswitch},\"eps3\":{eps3},\"tswitch2\":{tswitch2},\"interval\":{interval},\"overrelax\":{nor},\"seed\":{seed},\"therm\":{therm}}}\n", sides, tflow);
    let t0 = Instant::now();
    let (mut links, mut sw, mut done) = if resume { match load_ckpt(&ckpath, g.vol*4) { Some(x) => { eprintln!("resumed sw={} nmeas={}", x.1, x.2); x } None => panic!("no ckpt") } }
        else { let mut r = Rng(splitmix(seed ^ 0x5151)); ((0..g.vol*4).map(|_| random_su2(&mut r)).collect(), 0u64, 0u64) };
    if !resume {
        for k in 0..therm { sweep(&mut links, &g, &classes, beta, nor, sw, seed, nth); sw += 1;
            if k % 50 == 0 { eprintln!("therm {k} {:.1}s plaq={:.6}", t0.elapsed().as_secs_f64(), plaq4(&links, &g, nth)); } }
        eprintln!("therm done {:.1}s plaq={:.6}", t0.elapsed().as_secs_f64(), plaq4(&links, &g, nth));
        let mut f = std::fs::File::create(&datpath).unwrap(); f.write_all(hdr.as_bytes()).unwrap();
        save_ckpt(&ckpath, &links, sw, 0);
    }
    let reclen = if plaq_only { 1 } else { 1 + tflow.len()*(1 + sides.len()*3*lt) };
    let mut f = std::fs::OpenOptions::new().read(true).write(true).open(&datpath).unwrap();
    // truncate to header + done records (drop records after last checkpoint)
    let hlen = { let mut b = Vec::new(); f.read_to_end(&mut b).unwrap(); b.iter().position(|&c| c == b'\n').unwrap() + 1 };
    f.set_len((hlen + done as usize * reclen * 8) as u64).unwrap(); f.seek(SeekFrom::End(0)).unwrap();
    let mut fa = links.clone(); let mut fb = links.clone();
    let tm = Instant::now(); let mut since = 0usize;
    while (done as usize) < meas {
        for _ in 0..interval { sweep(&mut links, &g, &classes, beta, nor, sw, seed, nth); sw += 1; }
        let mut rec = vec![plaq4(&links, &g, nth)];
        if !plaq_only {
            fa.copy_from_slice(&links); let mut tcur = 0.0;
            for &tf in &tflow {
                while tcur < tf - 1e-9 { let h = (if tcur < tswitch - 1e-9 { eps.min(tswitch - tcur) } else if tcur < tswitch2 - 1e-9 { eps2.min(tswitch2 - tcur) } else { eps3 }).min(tf - tcur); flow_step(&fa, &mut fb, &g, h, nth); std::mem::swap(&mut fa, &mut fb); tcur += h; }
                let (r, es) = loops(&fa, &g, &sides, nth); rec.push(es); for v in r { rec.extend(v); }
            }
        }
        let bytes: Vec<u8> = rec.iter().flat_map(|x| x.to_le_bytes()).collect(); f.write_all(&bytes).unwrap();
        done += 1; since += 1;
        if since >= ckpt || done as usize == meas { f.sync_all().unwrap(); save_ckpt(&ckpath, &links, sw, done); since = 0; }
        if done % 10 == 0 || done < 3 { eprintln!("meas {done}/{meas} {:.1}s ({:.2}s/meas) plaq={:.6} Es_last={:.5}", t0.elapsed().as_secs_f64(), tm.elapsed().as_secs_f64()/ (done as f64).max(1.0), rec[0], if rec.len()>1 { rec[rec.len()-1-sides.len()*3*lt] } else { 0.0 }); }
    }
    eprintln!("done {:.1}s", t0.elapsed().as_secs_f64());
}
