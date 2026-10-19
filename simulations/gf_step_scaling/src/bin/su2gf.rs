//! SU(2) pure gauge, Wilson action, periodic 4D torus L^4.
//! Update: Kennedy-Pendleton heatbath + n_or microcanonical overrelaxation per sweep.
//! Observables: Wilson-flow (Luescher RK3, step eps) clover energy density E_c(t),
//! plaquette-definition E_p(t), clover topological charge Q(t), at flow times t = c^2 L^2/8.
//! Single-threaded by design (resource rules); run several processes with nice.
use gf_step_scaling::*;
use std::io::Write;

type Q = [f64; 4];
const PI: f64 = std::f64::consts::PI;

/// 't Hooft twist n_12 = 1 (SU(2): z = -1) in the (x0,x1) plane of the code (= Ramos' x1-x2 plane), arXiv:1409.1445:
/// the (0,1)-plaquettes with lower-left corner at x0 = x1 = L-1 (one per (x2,x3)) enter action, force and observables multiplied by z.
static TWIST: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
#[inline]
fn tz(g: &Geom, base: usize, mu: usize, nu: usize) -> f64 {
    if !TWIST.load(std::sync::atomic::Ordering::Relaxed) { return 1.0; }
    if !((mu == 0 && nu == 1) || (mu == 1 && nu == 0)) { return 1.0; }
    let l = g.l;
    if base % l == l - 1 && (base / l) % l == l - 1 { -1.0 } else { 1.0 }
}
#[inline]
fn qscale(a: &Q, f: f64) -> Q { [a[0] * f, a[1] * f, a[2] * f, a[3] * f] }

#[inline]
fn qmul(a: &Q, b: &Q) -> Q {
    [
        a[0] * b[0] - a[1] * b[1] - a[2] * b[2] - a[3] * b[3],
        a[0] * b[1] + b[0] * a[1] - (a[2] * b[3] - a[3] * b[2]),
        a[0] * b[2] + b[0] * a[2] - (a[3] * b[1] - a[1] * b[3]),
        a[0] * b[3] + b[0] * a[3] - (a[1] * b[2] - a[2] * b[1]),
    ]
}
#[inline]
fn qd(a: &Q) -> Q {
    [a[0], -a[1], -a[2], -a[3]]
}
#[inline]
fn qadd(a: &mut Q, b: &Q) {
    for i in 0..4 {
        a[i] += b[i];
    }
}
fn qnorm(a: &mut Q) {
    let n = (a[0] * a[0] + a[1] * a[1] + a[2] * a[2] + a[3] * a[3]).sqrt();
    for i in 0..4 {
        a[i] /= n;
    }
}
#[inline]
fn qexp(v: [f64; 3]) -> Q {
    let n = (v[0] * v[0] + v[1] * v[1] + v[2] * v[2]).sqrt();
    if n < 1e-300 {
        return [1.0, 0.0, 0.0, 0.0];
    }
    let (s, c) = n.sin_cos();
    [c, s * v[0] / n, s * v[1] / n, s * v[2] / n]
}

fn staple(l: &[Q], g: &Geom, s: usize, mu: usize) -> Q {
    let mut c = [0.0; 4];
    let sm = g.up[s][mu];
    for nu in 0..4 {
        if nu == mu {
            continue;
        }
        let su = g.up[s][nu];
        let t1 = qscale(&qmul(&qmul(&l[sm * 4 + nu], &qd(&l[su * 4 + mu])), &qd(&l[s * 4 + nu])), tz(g, s, mu, nu));
        let sd = g.dn[s][nu];
        let smd = g.up[sd][mu];
        let t2 = qscale(&qmul(&qmul(&qd(&l[smd * 4 + nu]), &qd(&l[sd * 4 + mu])), &l[sd * 4 + nu]), tz(g, sd, mu, nu));
        qadd(&mut c, &t1);
        qadd(&mut c, &t2);
    }
    c
}

fn sample_a0(rng: &mut Rng, alpha: f64) -> f64 {
    // density ~ sqrt(1-a0^2) exp(alpha a0)  (Kennedy-Pendleton)
    loop {
        let r1 = rng.uni();
        let r2 = rng.uni();
        let r3 = rng.uni();
        let r4 = rng.uni();
        let c = (2.0 * PI * r2).cos();
        let delta = -(r1.ln() + c * c * r3.ln()) / alpha;
        if r4 * r4 <= 1.0 - 0.5 * delta {
            return 1.0 - delta;
        }
    }
}

fn heatbath_link(l: &mut [Q], g: &Geom, s: usize, mu: usize, beta: f64, rng: &mut Rng) {
    let c = staple(l, g, s, mu);
    let k = (c[0] * c[0] + c[1] * c[1] + c[2] * c[2] + c[3] * c[3]).sqrt();
    if k < 1e-12 {
        // random link
        let a0 = 2.0 * rng.uni() - 1.0;
        let r = (1.0 - a0 * a0).sqrt();
        let z = 2.0 * rng.uni() - 1.0;
        let ph = 2.0 * PI * rng.uni();
        let rr = (1.0 - z * z).sqrt();
        l[s * 4 + mu] = [a0, r * rr * ph.cos(), r * rr * ph.sin(), r * z];
        return;
    }
    let vh = [c[0] / k, c[1] / k, c[2] / k, c[3] / k];
    let a0 = sample_a0(rng, beta * k);
    let r = (1.0 - a0 * a0).max(0.0).sqrt();
    let z = 2.0 * rng.uni() - 1.0;
    let ph = 2.0 * PI * rng.uni();
    let rr = (1.0 - z * z).sqrt();
    let x = [a0, r * rr * ph.cos(), r * rr * ph.sin(), r * z];
    let mut u = qmul(&x, &qd(&vh));
    qnorm(&mut u);
    l[s * 4 + mu] = u;
}

fn overrelax_link(l: &mut [Q], g: &Geom, s: usize, mu: usize) {
    let c = staple(l, g, s, mu);
    let k = (c[0] * c[0] + c[1] * c[1] + c[2] * c[2] + c[3] * c[3]).sqrt();
    if k < 1e-12 {
        return;
    }
    let vh = [c[0] / k, c[1] / k, c[2] / k, c[3] / k];
    let vd = qd(&vh);
    let mut u = qmul(&qmul(&vd, &qd(&l[s * 4 + mu])), &vd);
    qnorm(&mut u);
    l[s * 4 + mu] = u;
}

fn sweep(l: &mut [Q], g: &Geom, beta: f64, nor: usize, rng: &mut Rng) {
    for s in 0..g.vol {
        for mu in 0..4 {
            heatbath_link(l, g, s, mu, beta, rng);
        }
    }
    for _ in 0..nor {
        for s in 0..g.vol {
            for mu in 0..4 {
                overrelax_link(l, g, s, mu);
            }
        }
    }
}

const PLANES: [(usize, usize); 6] = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)];

#[inline]
fn leaf1(l: &[Q], g: &Geom, s: usize, mu: usize, nu: usize) -> Q {
    let sm = g.up[s][mu];
    let sn = g.up[s][nu];
    qmul(&qmul(&qmul(&l[s * 4 + mu], &l[sm * 4 + nu]), &qd(&l[sn * 4 + mu])), &qd(&l[s * 4 + nu]))
}

/// returns (E_clover, E_plaq, Q_clover), per-site-averaged E, summed Q
fn measure(l: &[Q], g: &Geom) -> (f64, f64, f64) {
    let mut ec = 0.0;
    let mut ep = 0.0;
    let mut qt = 0.0;
    for s in 0..g.vol {
        let mut gv = [[0.0f64; 3]; 6];
        for (pi, &(mu, nu)) in PLANES.iter().enumerate() {
            let l1 = qscale(&leaf1(l, g, s, mu, nu), tz(g, s, mu, nu));
            ep += 4.0 * (1.0 - l1[0]);
            // L2 = U_nu(x) U_mu(x-mu+nu)^† U_nu(x-mu)^† U_mu(x-mu)
            let sdm = g.dn[s][mu];
            let sdm_up_nu = g.up[sdm][nu];
            let l2 = qscale(&qmul(&qmul(&qmul(&l[s * 4 + nu], &qd(&l[sdm_up_nu * 4 + mu])), &qd(&l[sdm * 4 + nu])), &l[sdm * 4 + mu]), tz(g, sdm, mu, nu));
            // L3 = U_mu(x-mu)^† U_nu(x-mu-nu)^† U_mu(x-mu-nu) U_nu(x-nu)
            let sdn = g.dn[s][nu];
            let sdmdn = g.dn[sdm][nu];
            let l3 = qscale(&qmul(&qmul(&qmul(&qd(&l[sdm * 4 + mu]), &qd(&l[sdmdn * 4 + nu])), &l[sdmdn * 4 + mu]), &l[sdn * 4 + nu]), tz(g, sdmdn, mu, nu));
            // L4 = U_nu(x-nu)^† U_mu(x-nu) U_nu(x+mu-nu) U_mu(x)^†
            let sup_dn = g.up[sdn][mu];
            let l4 = qscale(&qmul(&qmul(&qmul(&qd(&l[sdn * 4 + nu]), &l[sdn * 4 + mu]), &l[sup_dn * 4 + nu]), &qd(&l[s * 4 + mu])), tz(g, sdn, mu, nu));
            let mut q = [0.0; 3];
            for k in 0..3 {
                q[k] = l1[k + 1] + l2[k + 1] + l3[k + 1] + l4[k + 1];
            }
            ec += (q[0] * q[0] + q[1] * q[1] + q[2] * q[2]) / 8.0;
            gv[pi] = [q[0] / 4.0, q[1] / 4.0, q[2] / 4.0];
        }
        let dot = |a: &[f64; 3], b: &[f64; 3]| a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
        // planes: 0:(01) 1:(02) 2:(03) 3:(12) 4:(13) 5:(23)
        qt += dot(&gv[0], &gv[5]) - dot(&gv[1], &gv[4]) + dot(&gv[2], &gv[3]);
    }
    (ec / g.vol as f64, ep / g.vol as f64, qt / (2.0 * PI * PI))
}

fn avg_plaq(l: &[Q], g: &Geom) -> f64 {
    let mut p = 0.0;
    for s in 0..g.vol {
        for &(mu, nu) in PLANES.iter() {
            p += leaf1(l, g, s, mu, nu)[0] * tz(g, s, mu, nu);
        }
    }
    p / (6.0 * g.vol as f64)
}

fn zfield(l: &[Q], g: &Geom, eps: f64, z: &mut [[f64; 3]]) {
    for s in 0..g.vol {
        for mu in 0..4 {
            let c = staple(l, g, s, mu);
            let m = qmul(&l[s * 4 + mu], &c);
            z[s * 4 + mu] = [-eps * m[1], -eps * m[2], -eps * m[3]];
        }
    }
}

/// Staple sum over the 18 rectangular (1x2 / 2x1) loops containing link (s,mu); loop = U_mu(x) * C.
fn rect_staple(l: &[Q], g: &Geom, s: usize, mu: usize) -> Q {
    let mut c = [0.0; 4];
    let u = |x: usize, m: usize| -> &Q { &l[x * 4 + m] };
    let xp = g.up[s][mu];           // x+mu
    let xpp = g.up[xp][mu];         // x+2mu
    let xm = g.dn[s][mu];           // x-mu
    for nu in 0..4 {
        if nu == mu { continue; }
        let xn = g.up[s][nu];       // x+nu
        let xd = g.dn[s][nu];       // x-nu
        // --- A1(+nu): U_mu(x+mu) U_nu(x+2mu) U_mu^+(x+mu+nu) U_mu^+(x+nu) U_nu^+(x)
        let t = qmul(&qmul(&qmul(&qmul(u(xp, mu), u(xpp, nu)), &qd(u(g.up[xp][nu], mu))), &qd(u(xn, mu))), &qd(u(s, nu)));
        qadd(&mut c, &t);
        // --- A1(-nu): U_mu(x+mu) U_nu^+(x+2mu-nu) U_mu^+(x+mu-nu) U_mu^+(x-nu) U_nu(x-nu)
        let t = qmul(&qmul(&qmul(&qmul(u(xp, mu), &qd(u(g.dn[xpp][nu], nu))), &qd(u(g.dn[xp][nu], mu))), &qd(u(xd, mu))), u(xd, nu));
        qadd(&mut c, &t);
        // --- A2(+nu): U_nu(x+mu) U_mu^+(x+nu) U_mu^+(x-mu+nu) U_nu^+(x-mu) U_mu(x-mu)
        let t = qmul(&qmul(&qmul(&qmul(u(xp, nu), &qd(u(xn, mu))), &qd(u(g.up[xm][nu], mu))), &qd(u(xm, nu))), u(xm, mu));
        qadd(&mut c, &t);
        // --- A2(-nu): U_nu^+(x+mu-nu) U_mu^+(x-nu) U_mu^+(x-mu-nu) U_nu(x-mu-nu) U_mu(x-mu)
        let xmd = g.dn[xm][nu];
        let t = qmul(&qmul(&qmul(&qmul(&qd(u(g.dn[xp][nu], nu)), &qd(u(xd, mu))), &qd(u(xmd, mu))), u(xmd, nu)), u(xm, mu));
        qadd(&mut c, &t);
        // --- B(+2nu): U_nu(x+mu) U_nu(x+mu+nu) U_mu^+(x+2nu) U_nu^+(x+nu) U_nu^+(x)
        let xn2 = g.up[xn][nu];
        let t = qmul(&qmul(&qmul(&qmul(u(xp, nu), u(g.up[xp][nu], nu)), &qd(u(xn2, mu))), &qd(u(xn, nu))), &qd(u(s, nu)));
        qadd(&mut c, &t);
        // --- B(-2nu): U_nu^+(x+mu-nu) U_nu^+(x+mu-2nu) U_mu^+(x-2nu) U_nu(x-2nu) U_nu(x-nu)
        let xd2 = g.dn[xd][nu];
        let t = qmul(&qmul(&qmul(&qmul(&qd(u(g.dn[xp][nu], nu)), &qd(u(g.dn[g.dn[xp][nu]][nu], nu))), &qd(u(xd2, mu))), u(xd2, nu)), u(xd, nu));
        qadd(&mut c, &t);
    }
    c
}

/// vector part of U_mu(x) * C
#[inline]
fn vec3(m: &Q) -> [f64; 3] { [m[1], m[2], m[3]] }

/// Zeuthen-flow force field  Z = -eps (1 + (1/12) nabla*_mu nabla_mu) [c0 * plaquette part + c1 * rectangle part],
/// Luescher-Weisz tree-level coefficients c0 = 5/3, c1 = -1/12 (Ramos-Sint, arXiv:1508.05552, eq. (5)).
/// `f` is a scratch buffer of the same size as `z`.
fn zfield_zeuthen(l: &[Q], g: &Geom, eps: f64, z: &mut [[f64; 3]], f: &mut [[f64; 3]]) {
    assert!(!TWIST.load(std::sync::atomic::Ordering::Relaxed), "Zeuthen flow (rectangles) not implemented with twisted b.c.");
    let c0 = 5.0 / 3.0;
    let c1 = -1.0 / 12.0;
    for s in 0..g.vol {
        for mu in 0..4 {
            let cp = staple(l, g, s, mu);
            let cr = rect_staple(l, g, s, mu);
            let mp = vec3(&qmul(&l[s * 4 + mu], &cp));
            let mr = vec3(&qmul(&l[s * 4 + mu], &cr));
            for k in 0..3 { f[s * 4 + mu][k] = c0 * mp[k] + c1 * mr[k]; }
        }
    }
    for s in 0..g.vol {
        for mu in 0..4 {
            let sp = g.up[s][mu];
            let sm = g.dn[s][mu];
            // Ad(U_mu(x)) f_mu(x+mu)  and  Ad(U_mu(x-mu))^-1 f_mu(x-mu)
            let u1 = l[s * 4 + mu];
            let a = f[sp * 4 + mu];
            let r1 = qmul(&qmul(&u1, &[0.0, a[0], a[1], a[2]]), &qd(&u1));
            let u2 = l[sm * 4 + mu];
            let b = f[sm * 4 + mu];
            let r2 = qmul(&qmul(&qd(&u2), &[0.0, b[0], b[1], b[2]]), &u2);
            let fc = f[s * 4 + mu];
            for k in 0..3 {
                let v = fc[k] + (r1[k + 1] + r2[k + 1] - 2.0 * fc[k]) / 12.0;
                z[s * 4 + mu][k] = -eps * v;
            }
        }
    }
}

fn apply(l: &mut [Q], z: &[[f64; 3]], a: &[[f64; 3]], b: &[[f64; 3]], ca: f64, cb: f64, cz: f64) {
    // l <- exp(cz*z + ca*a + cb*b) l   (z, a, b are Z-arrays; unused ones passed with 0 coef)
    for i in 0..l.len() {
        let v = [cz * z[i][0] + ca * a[i][0] + cb * b[i][0], cz * z[i][1] + ca * a[i][1] + cb * b[i][1], cz * z[i][2] + ca * a[i][2] + cb * b[i][2]];
        let e = qexp(v);
        l[i] = qmul(&e, &l[i]);
        qnorm(&mut l[i]);
    }
}

fn force(l: &[Q], g: &Geom, eps: f64, zeu: bool, z: &mut Vec<[f64; 3]>, scratch: &mut Vec<[f64; 3]>) {
    if zeu { zfield_zeuthen(l, g, eps, z, scratch); } else { zfield(l, g, eps, z); }
}

fn flow_step(l: &mut [Q], g: &Geom, eps: f64, zeu: bool, z0: &mut Vec<[f64; 3]>, z1: &mut Vec<[f64; 3]>, z2: &mut Vec<[f64; 3]>, scratch: &mut Vec<[f64; 3]>) {
    force(l, g, eps, zeu, z0, scratch);
    apply(l, z0, z0, z0, 0.0, 0.0, 0.25);
    force(l, g, eps, zeu, z1, scratch);
    apply(l, z1, z0, z0, -17.0 / 36.0, 0.0, 8.0 / 9.0);
    force(l, g, eps, zeu, z2, scratch);
    // exp(3/4 Z2 - 8/9 Z1 + 17/36 Z0)
    for i in 0..l.len() {
        let v = [
            0.75 * z2[i][0] - 8.0 / 9.0 * z1[i][0] + 17.0 / 36.0 * z0[i][0],
            0.75 * z2[i][1] - 8.0 / 9.0 * z1[i][1] + 17.0 / 36.0 * z0[i][1],
            0.75 * z2[i][2] - 8.0 / 9.0 * z1[i][2] + 17.0 / 36.0 * z0[i][2],
        ];
        let e = qexp(v);
        l[i] = qmul(&e, &l[i]);
        qnorm(&mut l[i]);
    }
}

/// flow a copy of l, measuring at each requested time
fn flow_measure(l0: &[Q], g: &Geom, times: &[f64], eps: f64, zeu: bool) -> Vec<(f64, f64, f64)> {
    let mut l = l0.to_vec();
    let n = l.len();
    let mut z0 = vec![[0.0; 3]; n];
    let mut z1 = vec![[0.0; 3]; n];
    let mut z2 = vec![[0.0; 3]; n];
    let mut scratch = vec![[0.0; 3]; if zeu { n } else { 0 }];
    let mut t = 0.0;
    let mut out = vec![];
    for &tt in times {
        if tt > t + 1e-12 {
            let ns = ((tt - t) / eps - 1e-9).ceil().max(1.0) as usize;
            let h = (tt - t) / ns as f64;
            for _ in 0..ns {
                flow_step(&mut l, g, h, zeu, &mut z0, &mut z1, &mut z2, &mut scratch);
            }
            t = tt;
        }
        out.push(measure(&l, g));
    }
    out
}

fn save_ckpt(path: &str, lat: usize, beta: f64, sweeps: u64, meas: u64, rng: &Rng, l: &[Q]) {
    let tmp = format!("{}.tmp", path);
    let mut b: Vec<u8> = vec![];
    b.extend((lat as u64).to_le_bytes());
    b.extend(beta.to_le_bytes());
    b.extend(sweeps.to_le_bytes());
    b.extend(meas.to_le_bytes());
    for w in rng.s {
        b.extend(w.to_le_bytes());
    }
    for q in l {
        for c in q {
            b.extend(c.to_le_bytes());
        }
    }
    std::fs::write(&tmp, b).unwrap();
    std::fs::rename(&tmp, path).unwrap();
}

fn load_ckpt(path: &str, lat: usize, beta: f64, l: &mut Vec<Q>, rng: &mut Rng) -> Option<(u64, u64)> {
    let b = std::fs::read(path).ok()?;
    let rd = |o: usize| u64::from_le_bytes(b[o..o + 8].try_into().unwrap());
    if rd(0) as usize != lat || f64::from_bits(rd(8)) != beta {
        return None;
    }
    let sweeps = rd(16);
    let meas = rd(24);
    for i in 0..4 {
        rng.s[i] = rd(32 + 8 * i);
    }
    let mut o = 64;
    for q in l.iter_mut() {
        for c in q.iter_mut() {
            *c = f64::from_bits(rd(o));
            o += 8;
        }
    }
    Some((sweeps, meas))
}

fn main() {
    let a = Args::parse();
    let lat: usize = a.get("L", 4);
    let beta: f64 = a.get("beta", 2.5);
    let therm: u64 = a.get("therm", 500);
    let nmeas: u64 = a.get("nmeas", 100);
    let sep: u64 = a.get("sep", 10);
    let nor: usize = a.get("nor", 4);
    let eps: f64 = a.get("eps", 0.02);
    let alt_eps: f64 = a.get("alt-eps", 0.0);
    let alt_every: u64 = a.get("alt-every", 10);
    let seed: u64 = a.get("seed", 12345);
    let start = a.gets("start", "cold");
    let cs = a.gets("c", "0.3,0.4,0.5");
    let extra = a.gets("times", "");
    let out = a.gets("out", "run");
    let ckpt_every: u64 = a.get("ckpt-every", 10);
    let test = a.get::<u32>("selftest", 0);
    let zeuthen: u32 = a.get("zeuthen", 0);   // 1: also measure the Zeuthen flow (LW force + a^2/12 nabla*nabla) on the same configs -> OUT.zeu.csv
    let zeu_eps: f64 = a.get("zeu-eps", eps);
    let twist: u32 = a.get("twist", 0);   // 1: twisted b.c. n_12 = 1 (Ramos TGF scheme); cold start = twist-eater (zero action)
    if twist > 0 { TWIST.store(true, std::sync::atomic::Ordering::Relaxed); }

    let g = Geom::new(lat);
    let times = flow_times(lat, &cs, &extra);
    let mut rng = Rng::new(seed);
    let mut l: Vec<Q> = vec![[1.0, 0.0, 0.0, 0.0]; g.vol * 4];
    if twist > 0 && start != "hot" {
        // twist eater: U_0(x) = i sigma_1 at x0 = L-1, U_1(x) = i sigma_2 at x1 = L-1, else 1  ->  A B A^+ B^+ = -1 on the twisted plaquettes, all U_p z_p = 1
        for s in 0..g.vol {
            if s % lat == lat - 1 { l[s * 4] = [0.0, 1.0, 0.0, 0.0]; }
            if (s / lat) % lat == lat - 1 { l[s * 4 + 1] = [0.0, 0.0, 1.0, 0.0]; }
        }
    }
    if start == "hot" {
        for q in l.iter_mut() {
            let mut v = [rng.uni() - 0.5, rng.uni() - 0.5, rng.uni() - 0.5, rng.uni() - 0.5];
            qnorm(&mut v);
            *q = v;
        }
    }
    if test == 2 {
        // staple consistency: sum of a0 of the 6 plaquettes containing a link vs a0(U*C)
        let sd = 37usize % g.vol;
        for mu in 0..4 {
            let c = staple(&l, &g, sd, mu);
            let uc = qmul(&l[sd * 4 + mu], &c);
            let mut direct = 0.0;
            for nu in 0..4 {
                if nu == mu { continue; }
                direct += leaf1(&l, &g, sd, mu, nu)[0] * tz(&g, sd, mu, nu);
                // plaquette at x-nu in plane (mu,nu): contains U_mu(x-nu+...)? it contains U_mu(x-nu) not U_mu(x); use plane (nu,mu) at x-nu: U_nu(x-nu)U_mu(x)U_nu(x+mu-nu)^† U_mu(x-nu)^†
                let sdn = g.dn[sd][nu];
                direct += leaf1(&l, &g, sdn, nu, mu)[0] * tz(&g, sdn, nu, mu);
            }
            println!("mu={} a0(UC)={:.12} direct={:.12}", mu, uc[0], direct);
        }
        return;
    }
    if test == 5 {
        // twisted b.c. self-tests (run with --twist 1 and default cold start = twist eater)
        let (ec, ep, qt) = measure(&l, &g);
        println!("twist-eater: twist={} plaq(with z)={:.15} Ec={:e} Ep={:e} Q={:e}", twist, avg_plaq(&l, &g), ec, ep, qt);
        let r0 = flow_measure(&l, &g, &[0.5, 1.0], 0.05, false);
        println!("twist-eater after flow t=0.5,1.0: Ec = {:e}, {:e}", r0[0].0, r0[1].0);
        // force on the twist eater vanishes
        let n = l.len(); let mut z = vec![[0.0; 3]; n]; zfield(&l, &g, 1.0, &mut z);
        let fm = z.iter().map(|v| (v[0] * v[0] + v[1] * v[1] + v[2] * v[2]).sqrt()).fold(0.0, f64::max);
        println!("max |force| on twist eater = {:e}", fm);
        // hot config: staple <-> plaquette consistency with z factors, gauge invariance of flowed E and of the action
        for q in l.iter_mut() { let mut v = [rng.uni() - 0.5, rng.uni() - 0.5, rng.uni() - 0.5, rng.uni() - 0.5]; qnorm(&mut v); *q = v; }
        let mut dmax = 0.0f64;
        for sd in [0usize, g.vol - 1, (lat - 1) + lat * (lat - 1), 37 % g.vol] {
            for mu in 0..4 {
                let uc = qmul(&l[sd * 4 + mu], &staple(&l, &g, sd, mu));
                let mut direct = 0.0;
                for nu in 0..4 { if nu == mu { continue; }
                    direct += leaf1(&l, &g, sd, mu, nu)[0] * tz(&g, sd, mu, nu);
                    let sdn = g.dn[sd][nu]; direct += leaf1(&l, &g, sdn, nu, mu)[0] * tz(&g, sdn, nu, mu);
                }
                dmax = dmax.max((uc[0] - direct).abs());
            }
        }
        println!("staple vs plaquettes (incl. twisted corner sites): max diff {:e}", dmax);
        let mut gt: Vec<Q> = Vec::new();
        for _ in 0..g.vol { let mut v = [rng.uni() - 0.5, rng.uni() - 0.5, rng.uni() - 0.5, rng.uni() - 0.5]; qnorm(&mut v); gt.push(v); }
        let mut l2 = l.clone();
        for s in 0..g.vol { for mu in 0..4 { l2[s * 4 + mu] = qmul(&qmul(&gt[s], &l[s * 4 + mu]), &qd(&gt[g.up[s][mu]])); } }
        println!("plaquette (with z): {:.14} vs gauge-transformed {:.14}", avg_plaq(&l, &g), avg_plaq(&l2, &g));
        let r1 = flow_measure(&l, &g, &[0.3, 0.8], 0.05, false); let r2 = flow_measure(&l2, &g, &[0.3, 0.8], 0.05, false);
        for i in 0..2 { println!("flowed Ec: {:.13} vs gauge-transformed {:.13} diff {:e}; Q {:.6} vs {:.6}", r1[i].0, r2[i].0, r1[i].0 - r2[i].0, r1[i].2, r2[i].2); }
        // the twist is not a gauge artefact: shifting the twisted corner by a gauge-equivalent relabelling must not matter, while the twist eater without z has action
        TWIST.store(false, std::sync::atomic::Ordering::Relaxed);
        let mut te: Vec<Q> = vec![[1.0, 0.0, 0.0, 0.0]; g.vol * 4];
        for s in 0..g.vol { if s % lat == lat - 1 { te[s * 4] = [0.0, 1.0, 0.0, 0.0]; } if (s / lat) % lat == lat - 1 { te[s * 4 + 1] = [0.0, 0.0, 1.0, 0.0]; } }
        println!("twist eater evaluated WITHOUT twist factors: plaq = {:.12} (expected 1 - 2/(6 L^2) = {:.12})", avg_plaq(&te, &g), 1.0 - 2.0 / (6.0 * (lat * lat) as f64));
        return;
    }
    if test == 4 {
        // Zeuthen force: (i) rectangle-staple identity, (ii) gauge covariance of the force field, (iii) E_c invariance after a Zeuthen flow
        for q in l.iter_mut() { let mut v = [rng.uni() - 0.5, rng.uni() - 0.5, rng.uni() - 0.5, rng.uni() - 0.5]; qnorm(&mut v); *q = v; }
        let mut lhs = 0.0; let mut rhs = 0.0;
        for s in 0..g.vol { for mu in 0..4 {
            lhs += qmul(&l[s * 4 + mu], &rect_staple(&l, &g, s, mu))[0];
            for nu in 0..4 { if nu == mu { continue; }
                let xp = g.up[s][mu]; let xpp = g.up[xp][mu]; let xn = g.up[s][nu];
                let r = qmul(&qmul(&qmul(&qmul(&qmul(&l[s * 4 + mu], &l[xp * 4 + mu]), &l[xpp * 4 + nu]), &qd(&l[g.up[xp][nu] * 4 + mu])), &qd(&l[xn * 4 + mu])), &qd(&l[s * 4 + nu]));
                rhs += r[0];
            }
        } }
        println!("rect identity: sum_links a0(U C_rect) = {:.10}, 6 * sum_rect a0 = {:.10}, diff = {:e}", lhs, 6.0 * rhs, lhs - 6.0 * rhs);
        let n = l.len();
        let mut z = vec![[0.0; 3]; n]; let mut sc = vec![[0.0; 3]; n];
        zfield_zeuthen(&l, &g, 1.0, &mut z, &mut sc);
        let mut gt: Vec<Q> = Vec::new();
        for _ in 0..g.vol { let mut v = [rng.uni() - 0.5, rng.uni() - 0.5, rng.uni() - 0.5, rng.uni() - 0.5]; qnorm(&mut v); gt.push(v); }
        let mut l2 = l.clone();
        for s in 0..g.vol { for mu in 0..4 { l2[s * 4 + mu] = qmul(&qmul(&gt[s], &l[s * 4 + mu]), &qd(&gt[g.up[s][mu]])); } }
        let mut z2 = vec![[0.0; 3]; n];
        zfield_zeuthen(&l2, &g, 1.0, &mut z2, &mut sc);
        let mut dmax = 0.0f64;
        for s in 0..g.vol { for mu in 0..4 {
            let a = z[s * 4 + mu];
            let r = qmul(&qmul(&gt[s], &[0.0, a[0], a[1], a[2]]), &qd(&gt[s]));
            for k in 0..3 { dmax = dmax.max((r[k + 1] - z2[s * 4 + mu][k]).abs()); }
        } }
        println!("gauge covariance of Zeuthen force: max|Z'-g Z g^+| = {:e}", dmax);
        let tt = [0.2f64, 0.5];
        let r1 = flow_measure(&l, &g, &tt, 0.05, true);
        let r2 = flow_measure(&l2, &g, &tt, 0.05, true);
        for i in 0..tt.len() { println!("Zeuthen flow t={} E_c: {:.12} vs gauge-transformed {:.12} diff {:e}", tt[i], r1[i].0, r2[i].0, r1[i].0 - r2[i].0); }
        return;
    }
    if test == 3 {
        // independent Metropolis check of the HB stationary distribution (same staple, different update)
        let mut acc = 0u64;
        let mut tot = 0u64;
        let mut ps = vec![];
        for sw in 0..(therm + 400) {
            for s in 0..g.vol {
                for mu in 0..4 {
                    let c = staple(&l, &g, s, mu);
                    for _ in 0..3 {
                        let mut d = [1.0, 0.5 * (rng.uni() - 0.5), 0.5 * (rng.uni() - 0.5), 0.5 * (rng.uni() - 0.5)];
                        qnorm(&mut d);
                        let mut un = qmul(&d, &l[s * 4 + mu]);
                        qnorm(&mut un);
                        let da = beta * (qmul(&un, &c)[0] - qmul(&l[s * 4 + mu], &c)[0]);
                        tot += 1;
                        if da >= 0.0 || rng.uni() < da.exp() {
                            l[s * 4 + mu] = un;
                            acc += 1;
                        }
                    }
                }
            }
            if sw >= therm {
                ps.push(avg_plaq(&l, &g));
            }
        }
        let m = ps.iter().sum::<f64>() / ps.len() as f64;
        println!("Metropolis beta={} L={} plaq={:.5} acc={:.3}", beta, lat, m, acc as f64 / tot as f64);
        return;
    }
    if test == 1 {
        // unitarity / algebra self-test + plaquette at cold start + strong coupling check
        let (ec, ep, qt) = measure(&l, &g);
        println!("cold: plaq={} Ec={} Ep={} Q={}", avg_plaq(&l, &g), ec, ep, qt);
        for _ in 0..200 {
            sweep(&mut l, &g, beta, nor, &mut rng);
        }
        let mut n = 0.0f64;
        for q in &l {
            n = n.max(((q[0] * q[0] + q[1] * q[1] + q[2] * q[2] + q[3] * q[3]) - 1.0).abs());
        }
        println!("beta={} L={} after 200 sweeps: plaq={} max|norm-1|={:e}", beta, lat, avg_plaq(&l, &g), n);
        return;
    }

    let ck = format!("{}.ckpt", out);
    let (mut sweeps, mut meas) = (0u64, 0u64);
    let mut resumed = false;
    if let Some((s, m)) = load_ckpt(&ck, lat, beta, &mut l, &mut rng) {
        sweeps = s;
        meas = m;
        resumed = true;
        eprintln!("resumed from checkpoint: sweeps={} meas={}", sweeps, meas);
    }
    let csv_path = format!("{}.csv", out);
    let mut csv = std::fs::OpenOptions::new().create(true).append(true).open(&csv_path).unwrap();
    let mut altcsv = std::fs::OpenOptions::new().create(true).append(true).open(format!("{}.alt.csv", out)).unwrap();
    let mut zcsv = if zeuthen > 0 { Some(std::fs::OpenOptions::new().create(true).append(true).open(format!("{}.zeu.csv", out)).unwrap()) } else { None };
    let mut plq = std::fs::OpenOptions::new().create(true).append(true).open(format!("{}.plaq", out)).unwrap();
    if !resumed {
        let hdr = format!(
            "# su2gf L={} beta={} therm={} sep={} nor={} eps={} alt_eps={} seed={} start={}{} times={:?}\n# cols: meas sweep plaq then per time t: Ec Ep Q\n",
            lat, beta, therm, sep, nor, eps, alt_eps, seed, start, if twist > 0 { " twist=n12" } else { "" }, times
        );
        csv.write_all(hdr.as_bytes()).unwrap();
        altcsv.write_all(hdr.as_bytes()).unwrap();
        if let Some(zf) = zcsv.as_mut() { zf.write_all(hdr.replace("# su2gf", "# su2gf ZEUTHEN-flow(LW force + a2/12 nabla*nabla; same eps unless --zeu-eps)").as_bytes()).unwrap(); }
    }
    let t0 = std::time::Instant::now();
    while meas < nmeas {
        let target = if meas == 0 && sweeps < therm { therm } else { sweeps + sep };
        while sweeps < target {
            sweep(&mut l, &g, beta, nor, &mut rng);
            sweeps += 1;
            writeln!(plq, "{} {:.8}", sweeps, avg_plaq(&l, &g)).unwrap();
        }
        let res = flow_measure(&l, &g, &times, eps, false);
        let mut line = format!("{} {} {:.8}", meas, sweeps, avg_plaq(&l, &g));
        for (ec, ep, q) in &res {
            line += &format!(" {:.10e} {:.10e} {:.8}", ec, ep, q);
        }
        writeln!(csv, "{}", line).unwrap();
        if let Some(zf) = zcsv.as_mut() {
            let rz = flow_measure(&l, &g, &times, zeu_eps, true);
            let mut lz = format!("{} {} {:.8}", meas, sweeps, avg_plaq(&l, &g));
            for (ec, ep, q) in &rz { lz += &format!(" {:.10e} {:.10e} {:.8}", ec, ep, q); }
            writeln!(zf, "{}", lz).unwrap();
        }
        if alt_eps > 0.0 && meas % alt_every == 0 {
            let r2 = flow_measure(&l, &g, &times, alt_eps, false);
            let mut l2 = format!("{} {} {:.8}", meas, sweeps, avg_plaq(&l, &g));
            for (ec, ep, q) in &r2 {
                l2 += &format!(" {:.10e} {:.10e} {:.8}", ec, ep, q);
            }
            writeln!(altcsv, "{}", l2).unwrap();
        }
        meas += 1;
        if meas % ckpt_every == 0 || meas == nmeas {
            csv.flush().unwrap();
            if let Some(zf) = zcsv.as_mut() { zf.flush().unwrap(); }
            altcsv.flush().unwrap();
            plq.flush().unwrap();
            save_ckpt(&ck, lat, beta, sweeps, meas, &rng, &l);
            eprintln!("L={} beta={} meas={}/{} sweeps={} elapsed={:.1}s", lat, beta, meas, nmeas, sweeps, t0.elapsed().as_secs_f64());
        }
    }
}
