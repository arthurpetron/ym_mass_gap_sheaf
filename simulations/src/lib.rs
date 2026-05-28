//! SU(2) lattice-gauge Monte Carlo (heatbath + overrelaxation), dependency-free.
//!
//! Cross-check target: the average plaquette `<P>` must reproduce the
//! Python MVP (`computations/su2_mcmc.py`) within statistical error on a
//! small lattice.  This crate is the fast (Rust, multithreaded) engine
//! underpinning the heavy measurements (glueball mass, string tension);
//! it does the number-crunching and emits JSON for the Python plotting
//! pipeline to consume.
//!
//! Conventions.  SU(2) elements are unit quaternions `[a0, a1, a2, a3]`
//! with `U = a0*I + i (a . sigma)`, `Tr U = 2 a0`.  The Wilson action is
//! `S = beta * sum_plaq [ 1 - (1/2) Re Tr U_plaq ]`, so the average
//! plaquette reported here is `<P> = < (1/2) Re Tr U_plaq > = <a0(U_plaq)>`.

use std::f64::consts::PI;

// ---------------------------------------------------------------------------
// RNG: splitmix64 — fast, seedable, good enough for MC; supports independent
// per-(sweep, pass, link) streams for thread-count-independent determinism.
// ---------------------------------------------------------------------------

pub struct Rng {
    state: u64,
}

impl Rng {
    #[inline]
    pub fn seed(s: u64) -> Self {
        Rng { state: s }
    }

    #[inline]
    pub fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// Uniform in [0, 1).
    #[inline]
    pub fn next_f64(&mut self) -> f64 {
        (self.next_u64() >> 11) as f64 * (1.0 / (1u64 << 53) as f64)
    }

    /// Uniform in (0, 1] (safe for `ln`).
    #[inline]
    pub fn next_open(&mut self) -> f64 {
        1.0 - self.next_f64()
    }
}

#[inline]
fn splitmix(mut z: u64) -> u64 {
    z = z.wrapping_add(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// Independent stream seed for a given (global seed, sweep, pass, link).
#[inline]
fn stream_seed(global: u64, sweep: u64, pass: u64, link: usize) -> u64 {
    let mut s = splitmix(global ^ sweep.wrapping_mul(0xD1B5_4A32_D192_ED03));
    s = splitmix(s ^ pass.wrapping_mul(0xA0761_D6478BD642F));
    splitmix(s ^ (link as u64).wrapping_mul(0xE703_7ED1_A0B4_28DB))
}

// ---------------------------------------------------------------------------
// SU(2) quaternion algebra.
// ---------------------------------------------------------------------------

pub type Su2 = [f64; 4];

pub const ID: Su2 = [1.0, 0.0, 0.0, 0.0];

/// Quaternion (SU(2)) product `a * b`, with `U = a0 + i a.sigma`.
#[inline]
pub fn mul(a: Su2, b: Su2) -> Su2 {
    [
        a[0] * b[0] - a[1] * b[1] - a[2] * b[2] - a[3] * b[3],
        a[0] * b[1] + b[0] * a[1] - (a[2] * b[3] - a[3] * b[2]),
        a[0] * b[2] + b[0] * a[2] - (a[3] * b[1] - a[1] * b[3]),
        a[0] * b[3] + b[0] * a[3] - (a[1] * b[2] - a[2] * b[1]),
    ]
}

/// Hermitian conjugate (= inverse for SU(2)).
#[inline]
pub fn dag(a: Su2) -> Su2 {
    [a[0], -a[1], -a[2], -a[3]]
}

/// 4-dot product (= (1/2) Re Tr(a b^dagger)).
#[inline]
fn dot(a: Su2, b: Su2) -> f64 {
    a[0] * b[0] + a[1] * b[1] + a[2] * b[2] + a[3] * b[3]
}

#[inline]
fn norm(a: Su2) -> f64 {
    dot(a, a).sqrt()
}

#[inline]
fn scale(a: Su2, s: f64) -> Su2 {
    [a[0] * s, a[1] * s, a[2] * s, a[3] * s]
}

#[inline]
fn add(a: Su2, b: Su2) -> Su2 {
    [a[0] + b[0], a[1] + b[1], a[2] + b[2], a[3] + b[3]]
}

/// Renormalize back onto SU(2) (defends against float drift).
#[inline]
pub fn renorm(a: Su2) -> Su2 {
    let n = norm(a);
    if n > 0.0 {
        scale(a, 1.0 / n)
    } else {
        ID
    }
}

/// Uniform (Haar) random SU(2): a point on S^3.
fn random_su2(rng: &mut Rng) -> Su2 {
    // Marsaglia: two uniform disks.
    loop {
        let x1 = 2.0 * rng.next_f64() - 1.0;
        let y1 = 2.0 * rng.next_f64() - 1.0;
        let s1 = x1 * x1 + y1 * y1;
        if s1 >= 1.0 {
            continue;
        }
        let x2 = 2.0 * rng.next_f64() - 1.0;
        let y2 = 2.0 * rng.next_f64() - 1.0;
        let s2 = x2 * x2 + y2 * y2;
        if s2 >= 1.0 || s2 == 0.0 {
            continue;
        }
        let f = ((1.0 - s1) / s2).sqrt();
        return [x1, y1, x2 * f, y2 * f];
    }
}

// ---------------------------------------------------------------------------
// Lattice.
// ---------------------------------------------------------------------------

pub const DIM: usize = 4;

pub struct Lattice {
    pub l: usize,
    pub vol: usize,             // l^4
    pub links: Vec<Su2>,        // vol * DIM links, index = site*DIM + mu
    strides: [usize; DIM],      // site index strides per coordinate
}

impl Lattice {
    pub fn new_hot(l: usize, seed: u64) -> Self {
        assert!(l >= 2, "lattice size must be >= 2");
        let vol = l.pow(DIM as u32);
        let strides = [l * l * l, l * l, l, 1];
        let mut rng = Rng::seed(splitmix(seed ^ 0x5151_5151_5151_5151));
        let links = (0..vol * DIM).map(|_| random_su2(&mut rng)).collect();
        Lattice { l, vol, links, strides }
    }

    #[inline]
    pub fn coord(&self, site: usize, dir: usize) -> usize {
        (site / self.strides[dir]) % self.l
    }

    /// Neighbour site in +mu / -mu (periodic).
    #[inline]
    pub fn shift(&self, site: usize, mu: usize, fwd: bool) -> usize {
        let c = self.coord(site, mu);
        let st = self.strides[mu];
        if fwd {
            if c + 1 == self.l {
                site + st - self.l * st
            } else {
                site + st
            }
        } else if c == 0 {
            site + (self.l - 1) * st
        } else {
            site - st
        }
    }

    #[inline]
    fn link(&self, site: usize, mu: usize) -> Su2 {
        self.links[site * DIM + mu]
    }

    /// Parity (even/odd checkerboard) of a site.
    #[inline]
    fn parity(&self, site: usize) -> usize {
        let mut s = 0usize;
        for d in 0..DIM {
            s += self.coord(site, d);
        }
        s & 1
    }

    /// Sum of the 6 staples around link (site, mu): an (unnormalized) quaternion
    /// `A` with `(1/2) Re Tr(U A^dag) = sum over the 6 plaquettes of (1/2) Re Tr U_plaq`.
    fn staple(&self, site: usize, mu: usize) -> Su2 {
        // We accumulate the plaquette "completions" C such that
        // U_plaq = U_mu(x) * C, then return A = sum(C^dag), so that
        // (1/2) Re Tr(U_mu(x) A^dag) = sum over the 6 plaquettes of
        // (1/2) Re Tr U_plaq.  (dag is linear, so we conjugate the sum.)
        let mut a = [0.0; 4];
        for nu in 0..DIM {
            if nu == mu {
                continue;
            }
            // forward completion: U_nu(x+mu) U_mu(x+nu)^dag U_nu(x)^dag
            let x_pmu = self.shift(site, mu, true);
            let x_pnu = self.shift(site, nu, true);
            let fwd = mul(
                mul(self.link(x_pmu, nu), dag(self.link(x_pnu, mu))),
                dag(self.link(site, nu)),
            );
            // backward completion: U_nu(x-nu+mu)^dag U_mu(x-nu)^dag U_nu(x-nu)
            let x_mnu = self.shift(site, nu, false);
            let x_mnu_pmu = self.shift(x_mnu, mu, true);
            let bwd = mul(
                mul(dag(self.link(x_mnu_pmu, nu)), dag(self.link(x_mnu, mu))),
                self.link(x_mnu, nu),
            );
            a = add(a, add(fwd, bwd));
        }
        dag(a)
    }

    /// Average plaquette `<P> = < (1/2) Re Tr U_plaq >` over all plaquettes.
    pub fn avg_plaquette(&self) -> f64 {
        let mut sum = 0.0f64;
        let mut count = 0u64;
        for site in 0..self.vol {
            for mu in 0..DIM {
                for nu in (mu + 1)..DIM {
                    let x_pmu = self.shift(site, mu, true);
                    let x_pnu = self.shift(site, nu, true);
                    // U_mu(x) U_nu(x+mu) U_mu(x+nu)^dag U_nu(x)^dag
                    let up = mul(
                        mul(self.link(site, mu), self.link(x_pmu, nu)),
                        mul(dag(self.link(x_pnu, mu)), dag(self.link(site, nu))),
                    );
                    sum += up[0]; // (1/2) Re Tr = a0
                    count += 1;
                }
            }
        }
        sum / count as f64
    }
}

// ---------------------------------------------------------------------------
// Heatbath (Kennedy-Pendleton) + overrelaxation.
// ---------------------------------------------------------------------------

/// Sample `a0 ~ sqrt(1-a0^2) * exp(lambda * a0)` on [-1, 1].
fn sample_a0(lambda: f64, rng: &mut Rng) -> f64 {
    if lambda < 1e-9 {
        // Haar marginal ∝ sqrt(1-a0^2): rejection.
        loop {
            let a0 = 2.0 * rng.next_f64() - 1.0;
            if rng.next_f64() <= (1.0 - a0 * a0).sqrt() {
                return a0;
            }
        }
    }
    // Kennedy-Pendleton.
    for _ in 0..1000 {
        let r1 = rng.next_open();
        let r2 = rng.next_f64();
        let r3 = rng.next_open();
        let c = (2.0 * PI * r2).cos();
        let delta = -(r1.ln() + c * c * r3.ln()) / lambda;
        let r4 = rng.next_f64();
        if r4 * r4 <= 1.0 - 0.5 * delta {
            return 1.0 - delta;
        }
    }
    // Pathological fallback (lambda tiny / unlucky): Creutz rejection.
    loop {
        let a0 = 2.0 * rng.next_f64() - 1.0;
        if rng.next_f64() <= (1.0 - a0 * a0).sqrt() {
            return a0;
        }
    }
}

/// Uniform 3-vector on the sphere of radius `r`.
#[inline]
fn random_vec3(r: f64, rng: &mut Rng) -> [f64; 3] {
    let cos_t = 2.0 * rng.next_f64() - 1.0;
    let phi = 2.0 * PI * rng.next_f64();
    let sin_t = (1.0 - cos_t * cos_t).max(0.0).sqrt();
    [r * sin_t * phi.cos(), r * sin_t * phi.sin(), r * cos_t]
}

/// Heatbath update for one link given its staple sum `a`.
fn heatbath_link(a: Su2, beta: f64, rng: &mut Rng) -> Su2 {
    let k = norm(a);
    if k < 1e-12 {
        return random_su2(rng);
    }
    let v = scale(a, 1.0 / k);
    let lambda = beta * k;
    let w0 = sample_a0(lambda, rng);
    let wv = random_vec3((1.0 - w0 * w0).max(0.0).sqrt(), rng);
    let w = [w0, wv[0], wv[1], wv[2]];
    renorm(mul(w, v))
}

/// Microcanonical overrelaxation: reflect `u` about the staple direction.
fn overrelax_link(u: Su2, a: Su2) -> Su2 {
    let k = norm(a);
    if k < 1e-12 {
        return u;
    }
    let v = scale(a, 1.0 / k);
    renorm(mul(mul(v, dag(u)), v))
}

// ---------------------------------------------------------------------------
// Parallel checkerboard sweep.
// ---------------------------------------------------------------------------

/// One full sweep: a heatbath pass then `n_or` overrelaxation passes, each
/// done over the 8 (mu, parity) classes.  Within a class, links share no
/// plaquette, so the compute is exact under read-the-lattice / apply-after.
pub fn sweep(lat: &mut Lattice, beta: f64, n_or: usize, sweep_idx: u64, seed: u64, threads: usize) {
    // class index list cache reused across classes (rebuilt cheaply).
    for pass in 0..(1 + n_or) {
        let is_heatbath = pass == 0;
        for mu in 0..DIM {
            for parity in 0..2 {
                // gather link indices for this class
                let mut idx: Vec<usize> = Vec::with_capacity(lat.vol / 2);
                for site in 0..lat.vol {
                    if lat.parity(site) == parity {
                        idx.push(site * DIM + mu);
                    }
                }
                let pass_tag = ((pass as u64) << 8) | (parity as u64) << 2 | mu as u64;
                let new_vals = compute_class(
                    lat, &idx, beta, is_heatbath, sweep_idx, pass_tag, seed, threads,
                );
                for (j, &link_idx) in idx.iter().enumerate() {
                    lat.links[link_idx] = new_vals[j];
                }
            }
        }
    }
}

/// Parallel compute of new link values for one class (read-only on the lattice).
fn compute_class(
    lat: &Lattice,
    idx: &[usize],
    beta: f64,
    is_heatbath: bool,
    sweep_idx: u64,
    pass_tag: u64,
    seed: u64,
    threads: usize,
) -> Vec<Su2> {
    let n = idx.len();
    let mut out = vec![ID; n];
    let nthreads = threads.max(1).min(n.max(1));
    let chunk = (n + nthreads - 1) / nthreads;
    std::thread::scope(|s| {
        for (idx_chunk, out_chunk) in idx.chunks(chunk).zip(out.chunks_mut(chunk)) {
            s.spawn(move || {
                for (j, &link_idx) in idx_chunk.iter().enumerate() {
                    let site = link_idx / DIM;
                    let mu = link_idx % DIM;
                    let a = lat.staple(site, mu);
                    out_chunk[j] = if is_heatbath {
                        let mut rng = Rng::seed(stream_seed(seed, sweep_idx, pass_tag, link_idx));
                        heatbath_link(a, beta, &mut rng)
                    } else {
                        overrelax_link(lat.link(site, mu), a)
                    };
                }
            });
        }
    });
    out
}

// ---------------------------------------------------------------------------
// Driver.
// ---------------------------------------------------------------------------

pub struct McmcResult {
    pub l: usize,
    pub beta: f64,
    pub n_therm: usize,
    pub n_meas: usize,
    pub meas_interval: usize,
    pub plaquette_mean: f64,
    pub plaquette_stderr: f64,
    pub n_overrelax: usize,
    pub threads: usize,
}

#[allow(clippy::too_many_arguments)]
pub fn run_mcmc(
    l: usize,
    beta: f64,
    n_therm: usize,
    n_meas: usize,
    meas_interval: usize,
    n_overrelax: usize,
    seed: u64,
    threads: usize,
) -> McmcResult {
    let mut lat = Lattice::new_hot(l, seed);
    let mut sweep_idx: u64 = 0;
    for _ in 0..n_therm {
        sweep(&mut lat, beta, n_overrelax, sweep_idx, seed, threads);
        sweep_idx += 1;
    }
    let mut samples: Vec<f64> = Vec::new();
    let mut since = 0usize;
    for _ in 0..n_meas {
        sweep(&mut lat, beta, n_overrelax, sweep_idx, seed, threads);
        sweep_idx += 1;
        since += 1;
        if since >= meas_interval {
            samples.push(lat.avg_plaquette());
            since = 0;
        }
    }
    if samples.is_empty() {
        samples.push(lat.avg_plaquette());
    }
    let nm = samples.len() as f64;
    let mean = samples.iter().sum::<f64>() / nm;
    let var = if samples.len() > 1 {
        samples.iter().map(|x| (x - mean).powi(2)).sum::<f64>() / (nm - 1.0)
    } else {
        0.0
    };
    let stderr = (var / nm).sqrt();
    McmcResult {
        l,
        beta,
        n_therm,
        n_meas,
        meas_interval,
        plaquette_mean: mean,
        plaquette_stderr: stderr,
        n_overrelax,
        threads,
    }
}

// ---------------------------------------------------------------------------
// Glueball (0++) measurement: smeared zero-momentum spatial-plaquette
// operators + their connected correlation matrix C_ij(tau).
// ---------------------------------------------------------------------------

#[inline]
fn lget(links: &[Su2], site: usize, mu: usize) -> Su2 {
    links[site * DIM + mu]
}

/// Spatial staple sum for a spatial link (site, mu): same convention as the
/// action staple (A with (1/2)Re Tr(U A^dag) = sum of plaquettes), but with
/// nu restricted to spatial directions {1,2,3}.  Used for APE smearing.
fn spatial_staple_from(links: &[Su2], lat: &Lattice, site: usize, mu: usize) -> Su2 {
    let mut a = [0.0; 4];
    for nu in 1..DIM {
        if nu == mu {
            continue;
        }
        let x_pmu = lat.shift(site, mu, true);
        let x_pnu = lat.shift(site, nu, true);
        let fwd = mul(
            mul(lget(links, x_pmu, nu), dag(lget(links, x_pnu, mu))),
            dag(lget(links, site, nu)),
        );
        let x_mnu = lat.shift(site, nu, false);
        let x_mnu_pmu = lat.shift(x_mnu, mu, true);
        let bwd = mul(
            mul(dag(lget(links, x_mnu_pmu, nu)), dag(lget(links, x_mnu, mu))),
            lget(links, x_mnu, nu),
        );
        a = add(a, add(fwd, bwd));
    }
    dag(a)
}

/// One APE smearing step on the spatial links (temporal links copied through):
/// U' = renorm(U + alpha * spatial_staple(U)).
fn ape_smear_spatial(links: &[Su2], lat: &Lattice, alpha: f64) -> Vec<Su2> {
    let mut out = links.to_vec();
    for site in 0..lat.vol {
        for mu in 1..DIM {
            let s = spatial_staple_from(links, lat, site, mu);
            out[site * DIM + mu] = renorm(add(lget(links, site, mu), scale(s, alpha)));
        }
    }
    out
}

/// Zero-momentum 0++ operator on timeslice `t`: sum over spatial sites and the
/// 3 spatial planes of (1/2)Re Tr U_spatial-plaq, built from `links`.
fn timeslice_op(links: &[Su2], lat: &Lattice, t: usize) -> f64 {
    let mut sum = 0.0;
    let st0 = lat.l * lat.l * lat.l; // stride for x0
    let base = t * st0;
    for s in 0..st0 {
        let site = base + s; // sites with coord(.,0) == t (x0 is the slowest index)
        for i in 1..DIM {
            for j in (i + 1)..DIM {
                let x_pi = lat.shift(site, i, true);
                let x_pj = lat.shift(site, j, true);
                let up = mul(
                    mul(lget(links, site, i), lget(links, x_pi, j)),
                    mul(dag(lget(links, x_pj, i)), dag(lget(links, site, j))),
                );
                sum += up[0];
            }
        }
    }
    sum
}

pub struct GlueballData {
    pub l: usize,
    pub beta: f64,
    pub n_therm: usize,
    pub n_collected: usize,
    pub smear_levels: Vec<usize>,
    pub smear_alpha: f64,
    pub overrelax: usize,
    pub threads: usize,
    /// `<O_i>` (per-timeslice average) for each smearing level.
    pub mean_op: Vec<f64>,
    /// Connected correlator C_ij(tau) = <O_i(t) O_j(t+tau)> - <O_i><O_j>,
    /// indexed [i][j][tau], tau = 0..=l/2.
    pub corr: Vec<Vec<Vec<f64>>>,
}

/// Measure the 0++ glueball correlation matrix.  `smear_levels` must be
/// sorted ascending (e.g. [0, 4, 8, 16]); each is a smearing count at which
/// the operator is recorded, forming a variational basis.
#[allow(clippy::too_many_arguments)]
pub fn measure_glueball(
    l: usize,
    beta: f64,
    n_therm: usize,
    n_meas: usize,
    meas_interval: usize,
    n_overrelax: usize,
    smear_levels: &[usize],
    smear_alpha: f64,
    seed: u64,
    threads: usize,
) -> GlueballData {
    let nlev = smear_levels.len();
    let max_level = *smear_levels.iter().max().unwrap_or(&0);
    let tau_max = l / 2;

    let mut lat = Lattice::new_hot(l, seed);
    let mut sweep_idx: u64 = 0;
    for _ in 0..n_therm {
        sweep(&mut lat, beta, n_overrelax, sweep_idx, seed, threads);
        sweep_idx += 1;
    }

    let mut mean_op = vec![0.0f64; nlev];
    let mut corr = vec![vec![vec![0.0f64; tau_max + 1]; nlev]; nlev];
    let mut n_collected = 0usize;
    let mut since = 0usize;

    for _ in 0..n_meas {
        sweep(&mut lat, beta, n_overrelax, sweep_idx, seed, threads);
        sweep_idx += 1;
        since += 1;
        if since < meas_interval {
            continue;
        }
        since = 0;

        // op[i][t] for each smearing level i and timeslice t.
        let mut op = vec![vec![0.0f64; l]; nlev];
        let mut sm = lat.links.clone();
        let mut idx = 0usize;
        for level in 0..=max_level {
            while idx < nlev && smear_levels[idx] == level {
                for t in 0..l {
                    op[idx][t] = timeslice_op(&sm, &lat, t);
                }
                idx += 1;
            }
            if level < max_level {
                sm = ape_smear_spatial(&sm, &lat, smear_alpha);
            }
        }

        for i in 0..nlev {
            let si: f64 = op[i].iter().sum::<f64>() / l as f64;
            mean_op[i] += si;
            for j in 0..nlev {
                for tau in 0..=tau_max {
                    let mut acc = 0.0;
                    for t in 0..l {
                        acc += op[i][t] * op[j][(t + tau) % l];
                    }
                    corr[i][j][tau] += acc / l as f64;
                }
            }
        }
        n_collected += 1;
    }

    let nc = n_collected.max(1) as f64;
    for i in 0..nlev {
        mean_op[i] /= nc;
    }
    for i in 0..nlev {
        for j in 0..nlev {
            for tau in 0..=tau_max {
                corr[i][j][tau] = corr[i][j][tau] / nc - mean_op[i] * mean_op[j];
            }
        }
    }

    GlueballData {
        l,
        beta,
        n_therm,
        n_collected,
        smear_levels: smear_levels.to_vec(),
        smear_alpha,
        overrelax: n_overrelax,
        threads,
        mean_op,
        corr,
    }
}

// ---------------------------------------------------------------------------
// Tests.
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn is_unit(a: Su2) -> bool {
        (norm(a) - 1.0).abs() < 1e-9
    }

    #[test]
    fn su2_inverse() {
        let mut rng = Rng::seed(1);
        for _ in 0..1000 {
            let u = random_su2(&mut rng);
            assert!(is_unit(u));
            let prod = mul(u, dag(u));
            assert!((prod[0] - 1.0).abs() < 1e-9);
            assert!(prod[1].abs() < 1e-9 && prod[2].abs() < 1e-9 && prod[3].abs() < 1e-9);
        }
    }

    #[test]
    fn su2_product_stays_unit() {
        let mut rng = Rng::seed(2);
        for _ in 0..1000 {
            let a = random_su2(&mut rng);
            let b = random_su2(&mut rng);
            assert!(is_unit(mul(a, b)));
        }
    }

    #[test]
    fn cold_lattice_plaquette_is_one() {
        // all-identity lattice => every plaquette = identity => <P> = 1.
        let mut lat = Lattice::new_hot(4, 7);
        for u in lat.links.iter_mut() {
            *u = ID;
        }
        assert!((lat.avg_plaquette() - 1.0).abs() < 1e-12);
    }

    #[test]
    fn plaquette_in_range() {
        let lat = Lattice::new_hot(4, 9);
        let p = lat.avg_plaquette();
        assert!((-1.0..=1.0).contains(&p));
    }

    #[test]
    fn overrelax_preserves_action() {
        // overrelaxation must preserve (1/2)Re Tr(U A^dag) = dot(U, A).
        let mut rng = Rng::seed(3);
        for _ in 0..1000 {
            let u = random_su2(&mut rng);
            let a = scale(random_su2(&mut rng), 1.0 + 3.0 * rng.next_f64());
            let u2 = overrelax_link(u, a);
            assert!(is_unit(u2));
            assert!((dot(u, a) - dot(u2, a)).abs() < 1e-9);
        }
    }

    #[test]
    fn heatbath_stays_su2() {
        let mut rng = Rng::seed(4);
        for _ in 0..1000 {
            let a = scale(random_su2(&mut rng), 0.5 + 5.0 * rng.next_f64());
            let u = heatbath_link(a, 2.3, &mut rng);
            assert!(is_unit(u));
        }
    }

    #[test]
    fn determinism_independent_of_thread_count() {
        let a = run_mcmc(4, 2.3, 20, 20, 2, 1, 12345, 1);
        let b = run_mcmc(4, 2.3, 20, 20, 2, 1, 12345, 4);
        assert!((a.plaquette_mean - b.plaquette_mean).abs() < 1e-12);
    }

    #[test]
    fn glueball_correlator_sane() {
        // Connected 0++ correlator: positive at tau=0, decreasing, finite
        // positive effective mass for the smeared operator.
        let g = measure_glueball(8, 2.4, 300, 2000, 4, 4, &[0, 4, 8], 0.5, 7, 4);
        let top = g.smear_levels.len() - 1;
        let c = &g.corr[top][top];
        assert!(c[0] > 0.0, "C(0) must be positive, got {}", c[0]);
        assert!(c[0] > c[1], "C(0) should exceed C(1): {} vs {}", c[0], c[1]);
        let meff = (c[0] / c[1]).ln();
        assert!(meff > 0.0 && meff.is_finite(), "effective mass should be positive finite, got {meff}");
    }

    #[test]
    fn strong_coupling_plaquette_sanity() {
        // At small beta, <P> ~ beta/4 (strong-coupling expansion).
        let r = run_mcmc(6, 1.0, 200, 400, 4, 2, 999, 4);
        let expected = 1.0 / 4.0; // beta/4 at beta=1
        assert!(
            (r.plaquette_mean - expected).abs() < 0.05,
            "got <P>={} at beta=1, expected ~{}",
            r.plaquette_mean,
            expected
        );
    }
}
