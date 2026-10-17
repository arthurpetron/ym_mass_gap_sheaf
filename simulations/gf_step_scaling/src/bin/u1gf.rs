//! Compact U(1) pure gauge, Wilson action S = beta sum_p (1-cos theta_p), periodic 4D torus L^4.
//! Heatbath (von Mises, Best-Fisher) + overrelaxation. Wilson flow d theta/dt = -(1/beta) dS/dtheta,
//! clover E_c(t) = (1/2) sum_{mu<nu} G_{mu nu}^2 with G = (1/4) sum_leaves sin(theta_leaf), so that
//! t^2 <E> = g0^2 * N(c) with g0^2 = 1/beta (see analysis/gfana.py for N). Control for the SU(2) pipeline.
use gf_step_scaling::*;
use std::io::Write;

const PI: f64 = std::f64::consts::PI;

fn wrap(x: f64) -> f64 {
    let mut y = x % (2.0 * PI);
    if y > PI {
        y -= 2.0 * PI;
    } else if y <= -PI {
        y += 2.0 * PI;
    }
    y
}

/// returns (k, phi) with sum_i exp(i s_i) = k exp(i phi)
fn staple(l: &[f64], g: &Geom, s: usize, mu: usize) -> (f64, f64) {
    let (mut cr, mut ci) = (0.0, 0.0);
    let sm = g.up[s][mu];
    for nu in 0..4 {
        if nu == mu {
            continue;
        }
        let su = g.up[s][nu];
        let a1 = l[sm * 4 + nu] - l[su * 4 + mu] - l[s * 4 + nu];
        let sd = g.dn[s][nu];
        let smd = g.up[sd][mu];
        let a2 = -l[smd * 4 + nu] - l[sd * 4 + mu] + l[sd * 4 + nu];
        cr += a1.cos() + a2.cos();
        ci += a1.sin() + a2.sin();
    }
    ((cr * cr + ci * ci).sqrt(), ci.atan2(cr))
}

fn von_mises(rng: &mut Rng, kappa: f64) -> f64 {
    if kappa < 1e-8 {
        return PI * (2.0 * rng.uni() - 1.0);
    }
    let tau = 1.0 + (1.0 + 4.0 * kappa * kappa).sqrt();
    let rho = (tau - (2.0 * tau).sqrt()) / (2.0 * kappa);
    let r = (1.0 + rho * rho) / (2.0 * rho);
    loop {
        let u1 = rng.uni();
        let u2 = rng.uni();
        let u3 = rng.uni();
        let z = (PI * u1).cos();
        let f = (1.0 + r * z) / (r + z);
        let c = kappa * (r - f);
        if c * (2.0 - c) - u2 > 0.0 || (c / u2).ln() + 1.0 - c >= 0.0 {
            let th = f.clamp(-1.0, 1.0).acos();
            return if u3 > 0.5 { th } else { -th };
        }
    }
}

fn sweep(l: &mut [f64], g: &Geom, beta: f64, nor: usize, rng: &mut Rng) {
    for s in 0..g.vol {
        for mu in 0..4 {
            let (k, phi) = staple(l, g, s, mu);
            // weight exp(beta k cos(theta+phi))
            let psi = von_mises(rng, beta * k);
            l[s * 4 + mu] = wrap(psi - phi);
        }
    }
    for _ in 0..nor {
        for s in 0..g.vol {
            for mu in 0..4 {
                let (_k, phi) = staple(l, g, s, mu);
                l[s * 4 + mu] = wrap(-l[s * 4 + mu] - 2.0 * phi);
            }
        }
    }
}

const PLANES: [(usize, usize); 6] = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)];

fn angle1(l: &[f64], g: &Geom, s: usize, mu: usize, nu: usize) -> f64 {
    let sm = g.up[s][mu];
    let sn = g.up[s][nu];
    l[s * 4 + mu] + l[sm * 4 + nu] - l[sn * 4 + mu] - l[s * 4 + nu]
}

fn avg_plaq(l: &[f64], g: &Geom) -> f64 {
    let mut p = 0.0;
    for s in 0..g.vol {
        for &(mu, nu) in PLANES.iter() {
            p += angle1(l, g, s, mu, nu).cos();
        }
    }
    p / (6.0 * g.vol as f64)
}

/// (E_clover, E_plaq): E_p = (1/V) sum_x sum_{mu<nu} 2 (1 - cos theta_p)
fn measure(l: &[f64], g: &Geom) -> (f64, f64) {
    let mut ec = 0.0;
    let mut ep = 0.0;
    for s in 0..g.vol {
        for &(mu, nu) in PLANES.iter() {
            let a1 = angle1(l, g, s, mu, nu);
            ep += 2.0 * (1.0 - a1.cos());
            let sdm = g.dn[s][mu];
            let a2 = l[s * 4 + nu] - l[g.up[sdm][nu] * 4 + mu] - l[sdm * 4 + nu] + l[sdm * 4 + mu];
            let sdn = g.dn[s][nu];
            let sdmdn = g.dn[sdm][nu];
            let a3 = -l[sdm * 4 + mu] - l[sdmdn * 4 + nu] + l[sdmdn * 4 + mu] + l[sdn * 4 + nu];
            let a4 = -l[sdn * 4 + nu] + l[sdn * 4 + mu] + l[g.up[sdn][mu] * 4 + nu] - l[s * 4 + mu];
            let gg = 0.25 * (a1.sin() + a2.sin() + a3.sin() + a4.sin());
            ec += 0.5 * gg * gg;
        }
    }
    (ec / g.vol as f64, ep / g.vol as f64)
}

fn zfield(l: &[f64], g: &Geom, eps: f64, z: &mut [f64]) {
    for s in 0..g.vol {
        for mu in 0..4 {
            let sm = g.up[s][mu];
            let mut acc = 0.0;
            for nu in 0..4 {
                if nu == mu {
                    continue;
                }
                let su = g.up[s][nu];
                let a1 = l[s * 4 + mu] + l[sm * 4 + nu] - l[su * 4 + mu] - l[s * 4 + nu];
                let sd = g.dn[s][nu];
                let smd = g.up[sd][mu];
                let a2 = l[s * 4 + mu] - l[smd * 4 + nu] - l[sd * 4 + mu] + l[sd * 4 + nu];
                acc += a1.sin() + a2.sin();
            }
            z[s * 4 + mu] = -eps * acc;
        }
    }
}

fn flow_step(l: &mut [f64], g: &Geom, eps: f64, z0: &mut Vec<f64>, z1: &mut Vec<f64>, z2: &mut Vec<f64>) {
    zfield(l, g, eps, z0);
    for i in 0..l.len() {
        l[i] += 0.25 * z0[i];
    }
    zfield(l, g, eps, z1);
    for i in 0..l.len() {
        l[i] += 8.0 / 9.0 * z1[i] - 17.0 / 36.0 * z0[i];
    }
    zfield(l, g, eps, z2);
    for i in 0..l.len() {
        l[i] += 0.75 * z2[i] - 8.0 / 9.0 * z1[i] + 17.0 / 36.0 * z0[i];
    }
}

fn flow_measure(l0: &[f64], g: &Geom, times: &[f64], eps: f64) -> Vec<(f64, f64)> {
    let mut l = l0.to_vec();
    let n = l.len();
    let mut z0 = vec![0.0; n];
    let mut z1 = vec![0.0; n];
    let mut z2 = vec![0.0; n];
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

fn save_ckpt(path: &str, lat: usize, beta: f64, sweeps: u64, meas: u64, rng: &Rng, l: &[f64]) {
    let tmp = format!("{}.tmp", path);
    let mut b: Vec<u8> = vec![];
    b.extend((lat as u64).to_le_bytes());
    b.extend(beta.to_le_bytes());
    b.extend(sweeps.to_le_bytes());
    b.extend(meas.to_le_bytes());
    for w in rng.s {
        b.extend(w.to_le_bytes());
    }
    for c in l {
        b.extend(c.to_le_bytes());
    }
    std::fs::write(&tmp, b).unwrap();
    std::fs::rename(&tmp, path).unwrap();
}

fn load_ckpt(path: &str, lat: usize, beta: f64, l: &mut Vec<f64>, rng: &mut Rng) -> Option<(u64, u64)> {
    let b = std::fs::read(path).ok()?;
    let rd = |o: usize| u64::from_le_bytes(b[o..o + 8].try_into().unwrap());
    if rd(0) as usize != lat || f64::from_bits(rd(8)) != beta {
        return None;
    }
    let (sweeps, meas) = (rd(16), rd(24));
    for i in 0..4 {
        rng.s[i] = rd(32 + 8 * i);
    }
    let mut o = 64;
    for c in l.iter_mut() {
        *c = f64::from_bits(rd(o));
        o += 8;
    }
    Some((sweeps, meas))
}

fn main() {
    let a = Args::parse();
    let lat: usize = a.get("L", 4);
    let beta: f64 = a.get("beta", 1.1);
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
    let g = Geom::new(lat);
    let times = flow_times(lat, &cs, &extra);
    let mut rng = Rng::new(seed);
    let mut l = vec![0.0f64; g.vol * 4];
    if start == "hot" {
        for x in l.iter_mut() {
            *x = PI * (2.0 * rng.uni() - 1.0);
        }
    }
    let ck = format!("{}.ckpt", out);
    let (mut sweeps, mut meas) = (0u64, 0u64);
    let mut resumed = false;
    if let Some((s, m)) = load_ckpt(&ck, lat, beta, &mut l, &mut rng) {
        sweeps = s;
        meas = m;
        resumed = true;
    }
    let mut csv = std::fs::OpenOptions::new().create(true).append(true).open(format!("{}.csv", out)).unwrap();
    let mut altcsv = std::fs::OpenOptions::new().create(true).append(true).open(format!("{}.alt.csv", out)).unwrap();
    let mut plq = std::fs::OpenOptions::new().create(true).append(true).open(format!("{}.plaq", out)).unwrap();
    if !resumed {
        let hdr = format!(
            "# u1gf L={} beta={} therm={} sep={} nor={} eps={} alt_eps={} seed={} start={} times={:?}\n# cols: meas sweep plaq then per time t: Ec Ep\n",
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
        for (ec, ep) in &res {
            line += &format!(" {:.10e} {:.10e}", ec, ep);
        }
        writeln!(csv, "{}", line).unwrap();
        if alt_eps > 0.0 && meas % alt_every == 0 {
            let r2 = flow_measure(&l, &g, &times, alt_eps);
            let mut l2 = format!("{} {} {:.8}", meas, sweeps, avg_plaq(&l, &g));
            for (ec, ep) in &r2 {
                l2 += &format!(" {:.10e} {:.10e}", ec, ep);
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
