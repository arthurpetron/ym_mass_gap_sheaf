//! SU(2) pure gauge, Wilson action, periodic 4D torus L^4.
//! Update: Kennedy-Pendleton heatbath + n_or microcanonical overrelaxation per sweep.
//! Observables: Wilson-flow (Luescher RK3, step eps) clover energy density E_c(t),
//! plaquette-definition E_p(t), clover topological charge Q(t), at flow times t = c^2 L^2/8.
//! Single-threaded by design (resource rules); run several processes with nice.
use gf_step_scaling::*;
use std::io::Write;

type Q = [f64; 4];
const PI: f64 = std::f64::consts::PI;

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
        let t1 = qmul(&qmul(&l[sm * 4 + nu], &qd(&l[su * 4 + mu])), &qd(&l[s * 4 + nu]));
        let sd = g.dn[s][nu];
        let smd = g.up[sd][mu];
        let t2 = qmul(&qmul(&qd(&l[smd * 4 + nu]), &qd(&l[sd * 4 + mu])), &l[sd * 4 + nu]);
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
            let l1 = leaf1(l, g, s, mu, nu);
            ep += 4.0 * (1.0 - l1[0]);
            // L2 = U_nu(x) U_mu(x-mu+nu)^† U_nu(x-mu)^† U_mu(x-mu)
            let sdm = g.dn[s][mu];
            let sdm_up_nu = g.up[sdm][nu];
            let l2 = qmul(&qmul(&qmul(&l[s * 4 + nu], &qd(&l[sdm_up_nu * 4 + mu])), &qd(&l[sdm * 4 + nu])), &l[sdm * 4 + mu]);
            // L3 = U_mu(x-mu)^† U_nu(x-mu-nu)^† U_mu(x-mu-nu) U_nu(x-nu)
            let sdn = g.dn[s][nu];
            let sdmdn = g.dn[sdm][nu];
            let l3 = qmul(&qmul(&qmul(&qd(&l[sdm * 4 + mu]), &qd(&l[sdmdn * 4 + nu])), &l[sdmdn * 4 + mu]), &l[sdn * 4 + nu]);
            // L4 = U_nu(x-nu)^† U_mu(x-nu) U_nu(x+mu-nu) U_mu(x)^†
            let sup_dn = g.up[sdn][mu];
            let l4 = qmul(&qmul(&qmul(&qd(&l[sdn * 4 + nu]), &l[sdn * 4 + mu]), &l[sup_dn * 4 + nu]), &qd(&l[s * 4 + mu]));
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
            p += leaf1(l, g, s, mu, nu)[0];
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

fn apply(l: &mut [Q], z: &[[f64; 3]], a: &[[f64; 3]], b: &[[f64; 3]], ca: f64, cb: f64, cz: f64) {
    // l <- exp(cz*z + ca*a + cb*b) l   (z, a, b are Z-arrays; unused ones passed with 0 coef)
    for i in 0..l.len() {
        let v = [cz * z[i][0] + ca * a[i][0] + cb * b[i][0], cz * z[i][1] + ca * a[i][1] + cb * b[i][1], cz * z[i][2] + ca * a[i][2] + cb * b[i][2]];
        let e = qexp(v);
        l[i] = qmul(&e, &l[i]);
        qnorm(&mut l[i]);
    }
}

fn flow_step(l: &mut [Q], g: &Geom, eps: f64, z0: &mut Vec<[f64; 3]>, z1: &mut Vec<[f64; 3]>, z2: &mut Vec<[f64; 3]>) {
    zfield(l, g, eps, z0);
    apply(l, z0, z0, z0, 0.0, 0.0, 0.25);
    zfield(l, g, eps, z1);
    apply(l, z1, z0, z0, -17.0 / 36.0, 0.0, 8.0 / 9.0);
    zfield(l, g, eps, z2);
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
fn flow_measure(l0: &[Q], g: &Geom, times: &[f64], eps: f64) -> Vec<(f64, f64, f64)> {
    let mut l = l0.to_vec();
    let n = l.len();
    let mut z0 = vec![[0.0; 3]; n];
    let mut z1 = vec![[0.0; 3]; n];
    let mut z2 = vec![[0.0; 3]; n];
    let mut t = 0.0;
    let mut out = vec![];
    for &tt in times {
        if tt > t + 1e-12 {
            let ns = ((tt - t) / eps - 1e-9).ceil().max(1.0) as usize;
            let h = (tt - t) / ns as f64;
            for _ in 0..ns {
                flow_step(&mut l, g, h, &mut z0, &mut z1, &mut z2);
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

    let g = Geom::new(lat);
    let times = flow_times(lat, &cs, &extra);
    let mut rng = Rng::new(seed);
    let mut l: Vec<Q> = vec![[1.0, 0.0, 0.0, 0.0]; g.vol * 4];
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
                direct += leaf1(&l, &g, sd, mu, nu)[0];
                // plaquette at x-nu in plane (mu,nu): contains U_mu(x-nu+...)? it contains U_mu(x-nu) not U_mu(x); use plane (nu,mu) at x-nu: U_nu(x-nu)U_mu(x)U_nu(x+mu-nu)^† U_mu(x-nu)^†
                let sdn = g.dn[sd][nu];
                direct += leaf1(&l, &g, sdn, nu, mu)[0];
            }
            println!("mu={} a0(UC)={:.12} direct={:.12}", mu, uc[0], direct);
        }
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
    let mut plq = std::fs::OpenOptions::new().create(true).append(true).open(format!("{}.plaq", out)).unwrap();
    if !resumed {
        let hdr = format!(
            "# su2gf L={} beta={} therm={} sep={} nor={} eps={} alt_eps={} seed={} start={} times={:?}\n# cols: meas sweep plaq then per time t: Ec Ep Q\n",
            lat, beta, therm, sep, nor, eps, alt_eps, seed, start, times
        );
        csv.write_all(hdr.as_bytes()).unwrap();
        altcsv.write_all(hdr.as_bytes()).unwrap();
    }
    let t0 = std::time::Instant::now();
    while meas < nmeas {
        let target = if meas == 0 && sweeps < therm { therm } else { sweeps + sep };
        while sweeps < target {
            sweep(&mut l, &g, beta, nor, &mut rng);
            sweeps += 1;
            writeln!(plq, "{} {:.8}", sweeps, avg_plaq(&l, &g)).unwrap();
        }
        let res = flow_measure(&l, &g, &times, eps);
        let mut line = format!("{} {} {:.8}", meas, sweeps, avg_plaq(&l, &g));
        for (ec, ep, q) in &res {
            line += &format!(" {:.10e} {:.10e} {:.8}", ec, ep, q);
        }
        writeln!(csv, "{}", line).unwrap();
        if alt_eps > 0.0 && meas % alt_every == 0 {
            let r2 = flow_measure(&l, &g, &times, alt_eps);
            let mut l2 = format!("{} {} {:.8}", meas, sweeps, avg_plaq(&l, &g));
            for (ec, ep, q) in &r2 {
                l2 += &format!(" {:.10e} {:.10e} {:.8}", ec, ep, q);
            }
            writeln!(altcsv, "{}", l2).unwrap();
        }
        meas += 1;
        if meas % ckpt_every == 0 || meas == nmeas {
            csv.flush().unwrap();
            altcsv.flush().unwrap();
            plq.flush().unwrap();
            save_ckpt(&ck, lat, beta, sweeps, meas, &rng, &l);
            eprintln!("L={} beta={} meas={}/{} sweeps={} elapsed={:.1}s", lat, beta, meas, nmeas, sweeps, t0.elapsed().as_secs_f64());
        }
    }
}
