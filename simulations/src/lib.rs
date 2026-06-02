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

pub mod polymer;

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

/// Lattice geometry only (no link data), so it can be shared `Copy` into worker
/// threads without aliasing the mutable `links` buffer.
#[derive(Clone, Copy)]
pub struct Geom {
    pub l: usize,
    pub vol: usize,
    pub strides: [usize; DIM],
}

impl Geom {
    #[inline]
    fn coord(&self, site: usize, dir: usize) -> usize {
        (site / self.strides[dir]) % self.l
    }
    #[inline]
    fn shift(&self, site: usize, mu: usize, fwd: bool) -> usize {
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
}

/// Staple sum for link (site, mu) reading links through a raw base pointer.
/// Same convention as `Lattice::staple`.  Used by the parallel sweep workers,
/// which read neighbour links (other checkerboard classes, never written in the
/// current sub-sweep) and write only their own class's links.
///
/// SAFETY: `base` must point to a valid `[Su2; geom.vol*DIM]`, and the cells
/// read here (the neighbours of (site, mu)) must not be concurrently written.
#[inline]
unsafe fn staple_ptr(base: *const Su2, geom: &Geom, site: usize, mu: usize) -> Su2 {
    #[inline(always)]
    unsafe fn get(base: *const Su2, s: usize, m: usize) -> Su2 {
        *base.add(s * DIM + m)
    }
    let mut a = [0.0; 4];
    for nu in 0..DIM {
        if nu == mu {
            continue;
        }
        let x_pmu = geom.shift(site, mu, true);
        let x_pnu = geom.shift(site, nu, true);
        let fwd = mul(
            mul(get(base, x_pmu, nu), dag(get(base, x_pnu, mu))),
            dag(get(base, site, nu)),
        );
        let x_mnu = geom.shift(site, nu, false);
        let x_mnu_pmu = geom.shift(x_mnu, mu, true);
        let bwd = mul(
            mul(dag(get(base, x_mnu_pmu, nu)), dag(get(base, x_mnu, mu))),
            get(base, x_mnu, nu),
        );
        a = add(a, add(fwd, bwd));
    }
    dag(a)
}

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

    #[inline]
    pub fn geom(&self) -> Geom {
        Geom { l: self.l, vol: self.vol, strides: self.strides }
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

/// The 8 (mu, parity) checkerboard classes of link indices, indexed
/// `[mu*2 + parity]`.  Within a class, links share no plaquette, so a class can
/// be updated fully in parallel.  Precompute once per run (the partition is
/// fixed); rebuilding it every sweep was pure overhead.
pub fn build_classes(lat: &Lattice) -> Vec<Vec<usize>> {
    let mut classes: Vec<Vec<usize>> = vec![Vec::with_capacity(lat.vol / 2); DIM * 2];
    for site in 0..lat.vol {
        let p = lat.parity(site);
        for mu in 0..DIM {
            classes[mu * 2 + p].push(site * DIM + mu);
        }
    }
    classes
}

/// Update one checkerboard class link `idx[k]`, in place, via the base pointer.
/// SAFETY: caller guarantees `idx[k]` is unique among concurrently-running
/// workers (checkerboard), and that the staple neighbours of (site, mu) are not
/// concurrently written (they belong to other classes, updated in other
/// barrier-separated phases).
#[inline]
unsafe fn update_link(
    base: *mut Su2,
    geom: &Geom,
    link_idx: usize,
    beta: f64,
    is_heatbath: bool,
    sweep_idx: u64,
    pass_tag: u64,
    seed: u64,
) {
    let site = link_idx / DIM;
    let mu = link_idx % DIM;
    let a = staple_ptr(base, geom, site, mu);
    let v = if is_heatbath {
        let mut rng = Rng::seed(stream_seed(seed, sweep_idx, pass_tag, link_idx));
        heatbath_link(a, beta, &mut rng)
    } else {
        overrelax_link(*base.add(link_idx), a)
    };
    *base.add(link_idx) = v;
}

/// One full sweep: a heatbath pass then `n_or` overrelaxation passes, each over
/// the 8 (mu, parity) checkerboard classes.  Workers are spawned **once per
/// sweep** and march through all class sub-sweeps together, synchronized by a
/// barrier after each class so that every write of class C lands before any
/// neighbour read of class C+1.  (Spawning once per sweep instead of once per
/// class cut the OS-thread-creation overhead ~100x.)
///
/// Determinism: each link's heatbath RNG is seeded from
/// `(seed, sweep_idx, pass_tag, link_idx)`, independent of thread count, so the
/// result is bit-identical for any `threads`.
pub fn sweep(
    lat: &mut Lattice,
    beta: f64,
    n_or: usize,
    sweep_idx: u64,
    seed: u64,
    threads: usize,
    classes: &[Vec<usize>],
) {
    let nthreads = threads.max(1);
    let geom = lat.geom();

    if nthreads == 1 {
        let base = lat.links.as_mut_ptr();
        for pass in 0..(1 + n_or) {
            let is_heatbath = pass == 0;
            for mu in 0..DIM {
                for parity in 0..2 {
                    let pass_tag = ((pass as u64) << 8) | (parity as u64) << 2 | mu as u64;
                    for &link_idx in &classes[mu * 2 + parity] {
                        // SAFETY: serial; indices valid.
                        unsafe {
                            update_link(
                                base, &geom, link_idx, beta, is_heatbath, sweep_idx, pass_tag,
                                seed,
                            );
                        }
                    }
                }
            }
        }
        return;
    }

    let base = lat.links.as_mut_ptr() as usize; // usize so the closure is Send
    let barrier = std::sync::Barrier::new(nthreads);
    std::thread::scope(|s| {
        for tid in 0..nthreads {
            let barrier = &barrier;
            let geom = geom;
            let classes = &classes;
            s.spawn(move || {
                let base = base as *mut Su2;
                for pass in 0..(1 + n_or) {
                    let is_heatbath = pass == 0;
                    for mu in 0..DIM {
                        for parity in 0..2 {
                            let idx = &classes[mu * 2 + parity];
                            let pass_tag =
                                ((pass as u64) << 8) | (parity as u64) << 2 | mu as u64;
                            let n = idx.len();
                            let chunk = (n + nthreads - 1) / nthreads;
                            let lo = (tid * chunk).min(n);
                            let hi = ((tid + 1) * chunk).min(n);
                            for &link_idx in &idx[lo..hi] {
                                // SAFETY: idx values are pairwise distinct, the
                                // per-worker ranges are disjoint, and a class
                                // link's staple reads only other-class links
                                // (fixed during this phase).  The barrier below
                                // orders this phase's writes before the next.
                                unsafe {
                                    update_link(
                                        base, &geom, link_idx, beta, is_heatbath, sweep_idx,
                                        pass_tag, seed,
                                    );
                                }
                            }
                            barrier.wait();
                        }
                    }
                }
            });
        }
    });
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
    let classes = build_classes(&lat);
    let mut sweep_idx: u64 = 0;
    for _ in 0..n_therm {
        sweep(&mut lat, beta, n_overrelax, sweep_idx, seed, threads, &classes);
        sweep_idx += 1;
    }
    let mut samples: Vec<f64> = Vec::new();
    let mut since = 0usize;
    for _ in 0..n_meas {
        sweep(&mut lat, beta, n_overrelax, sweep_idx, seed, threads, &classes);
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
/// U' = renorm(U + alpha * spatial_staple(U)).  Parallel over site chunks; the
/// map is a pure function of `links`, so the result is independent of thread
/// count.
fn ape_smear_spatial(links: &[Su2], lat: &Lattice, alpha: f64, threads: usize) -> Vec<Su2> {
    let mut out = links.to_vec();
    let vol = lat.vol;
    let nthreads = threads.max(1).min(vol);
    let chunk_sites = (vol + nthreads - 1) / nthreads;
    std::thread::scope(|s| {
        for (ci, out_chunk) in out.chunks_mut(chunk_sites * DIM).enumerate() {
            let site0 = ci * chunk_sites;
            s.spawn(move || {
                let n = out_chunk.len() / DIM;
                for j in 0..n {
                    let site = site0 + j;
                    for mu in 1..DIM {
                        let st = spatial_staple_from(links, lat, site, mu);
                        out_chunk[j * DIM + mu] =
                            renorm(add(lget(links, site, mu), scale(st, alpha)));
                    }
                }
            });
        }
    });
    out
}

/// Zero-momentum spatial-plaquette sums per plane on timeslice `t`: returns
/// `(P_{12}(t), P_{13}(t), P_{23}(t))` where `P_{ij}(t)` is the sum over
/// spatial sites of `(1/2)Re Tr U_{plaq}` in plane `(i,j)`.  The A_1 (0++)
/// operator is the symmetric sum P_{12}+P_{13}+P_{23}; the E (2++) operators
/// are the two orthogonal cubic-irrep combinations
///     E_1 = (2 P_{23} - P_{12} - P_{13}) / sqrt(6),
///     E_2 = (P_{13} - P_{12}) / sqrt(2).
/// Loop order maps (i,j) -> plane index:
///   (1,2) -> 0,  (1,3) -> 1,  (2,3) -> 2.
fn timeslice_op_planes(links: &[Su2], lat: &Lattice, t: usize) -> [f64; 3] {
    let mut p = [0.0f64; 3];
    let st0 = lat.l * lat.l * lat.l; // stride for x0
    let base = t * st0;
    for s in 0..st0 {
        let site = base + s; // sites with coord(.,0) == t (x0 is the slowest index)
        let mut k = 0usize;
        for i in 1..DIM {
            for j in (i + 1)..DIM {
                let x_pi = lat.shift(site, i, true);
                let x_pj = lat.shift(site, j, true);
                let up = mul(
                    mul(lget(links, site, i), lget(links, x_pi, j)),
                    mul(dag(lget(links, x_pj, i)), dag(lget(links, site, j))),
                );
                p[k] += up[0];
                k += 1;
            }
        }
    }
    p
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
    /// Number of (contiguous) configuration bins for jackknife error analysis.
    pub n_bins: usize,
    /// Configs in each bin; `[n_bins]`.
    pub bin_counts: Vec<usize>,
    /// Per-bin UNSUBTRACTED operator sum: sum over the bin's configs of the
    /// per-timeslice mean (1/L) sum_t O_i(t).  `[n_bins][nlev]`.  The connected
    /// correlator on any jackknife sample is rebuilt downstream from these and
    /// `bin_corr_sum` (so the subtraction uses the leave-one-out mean).
    pub bin_op_sum: Vec<Vec<f64>>,
    /// Per-bin UNSUBTRACTED correlator sum: sum over the bin's configs of
    /// (1/L) sum_t O_i(t) O_j(t+tau).  `[n_bins][nlev][nlev][tau_max+1]`.
    pub bin_corr_sum: Vec<Vec<Vec<Vec<f64>>>>,
    /// `<O^E_a>` for each (smear i, E component a in {0,1}), flat-indexed as
    /// `mean_op_E[2*i + a]`.  Length `2*nlev`.  Component 0 = E_1, 1 = E_2.
    pub mean_op_E: Vec<f64>,
    /// Connected 2++ E-channel correlator `C^E_{(ia)(jb)}(tau)`, indexed
    /// `[2*i+a][2*j+b][tau]`.  Size `(2*nlev) x (2*nlev) x (tau_max+1)`.
    pub corr_E: Vec<Vec<Vec<f64>>>,
    /// Per-bin UNSUBTRACTED E-channel operator sum, `[n_bins][2*nlev]`.
    pub bin_op_E_sum: Vec<Vec<f64>>,
    /// Per-bin UNSUBTRACTED E-channel correlator sum,
    /// `[n_bins][2*nlev][2*nlev][tau_max+1]`.
    pub bin_corr_E_sum: Vec<Vec<Vec<Vec<f64>>>>,
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
    n_bins: usize,
    seed: u64,
    threads: usize,
) -> GlueballData {
    let nlev = smear_levels.len();
    let n_e = 2 * nlev; // E-channel operators: 2 per smear (E_1, E_2)
    let max_level = *smear_levels.iter().max().unwrap_or(&0);
    let tau_max = l / 2;

    // Contiguous binning of the collected configs for jackknife errors.  The
    // expected collected count is n_meas/meas_interval; clamp the bin count to
    // that and assign configs to bins by their collection index.
    let expected = (n_meas / meas_interval.max(1)).max(1);
    let n_bins = n_bins.clamp(1, expected);
    let bin_size = (expected + n_bins - 1) / n_bins;
    let mut bin_counts = vec![0usize; n_bins];
    let mut bin_op_sum = vec![vec![0.0f64; nlev]; n_bins];
    let mut bin_corr_sum = vec![vec![vec![vec![0.0f64; tau_max + 1]; nlev]; nlev]; n_bins];
    let mut bin_op_E_sum = vec![vec![0.0f64; n_e]; n_bins];
    let mut bin_corr_E_sum = vec![vec![vec![vec![0.0f64; tau_max + 1]; n_e]; n_e]; n_bins];

    let mut lat = Lattice::new_hot(l, seed);
    let classes = build_classes(&lat);
    let mut sweep_idx: u64 = 0;
    for _ in 0..n_therm {
        sweep(&mut lat, beta, n_overrelax, sweep_idx, seed, threads, &classes);
        sweep_idx += 1;
    }

    let mut n_collected = 0usize;
    let mut since = 0usize;

    for _ in 0..n_meas {
        sweep(&mut lat, beta, n_overrelax, sweep_idx, seed, threads, &classes);
        sweep_idx += 1;
        since += 1;
        if since < meas_interval {
            continue;
        }
        since = 0;

        // op_planes[i][t] = (P_{12}, P_{13}, P_{23}) per smear level i and
        // timeslice t.  A_1 (0++) and E (2++) operators are linear combinations.
        let mut op_planes = vec![vec![[0.0f64; 3]; l]; nlev];
        let mut sm = lat.links.clone();
        let mut idx = 0usize;
        for level in 0..=max_level {
            while idx < nlev && smear_levels[idx] == level {
                // parallel over timeslices (each independent).
                let row = &mut op_planes[idx];
                let sm_ref = &sm;
                let lat_ref = &lat;
                let nthreads = threads.max(1).min(l);
                let chunk = (l + nthreads - 1) / nthreads;
                std::thread::scope(|s| {
                    for (ci, rchunk) in row.chunks_mut(chunk).enumerate() {
                        let t0 = ci * chunk;
                        s.spawn(move || {
                            for (j, slot) in rchunk.iter_mut().enumerate() {
                                *slot = timeslice_op_planes(sm_ref, lat_ref, t0 + j);
                            }
                        });
                    }
                });
                idx += 1;
            }
            if level < max_level {
                sm = ape_smear_spatial(&sm, &lat, smear_alpha, threads);
            }
        }

        // Derive A_1 (0++) and E (2++) operators from per-plane sums.
        let inv_sqrt6 = 1.0 / 6.0f64.sqrt();
        let inv_sqrt2 = 1.0 / 2.0f64.sqrt();
        let mut op = vec![vec![0.0f64; l]; nlev]; // A_1 channel
        let mut op_e = vec![vec![0.0f64; l]; n_e]; // E channel: [2*smear + comp][t]
        for i in 0..nlev {
            for t in 0..l {
                let p = op_planes[i][t];
                op[i][t] = p[0] + p[1] + p[2]; // A_1: symmetric sum
                op_e[2 * i][t] = inv_sqrt6 * (2.0 * p[2] - p[0] - p[1]); // E_1
                op_e[2 * i + 1][t] = inv_sqrt2 * (p[1] - p[0]); // E_2
            }
        }

        let bin = (n_collected / bin_size).min(n_bins - 1);
        bin_counts[bin] += 1;
        // A_1 (0++) channel accumulation -- unchanged from the original.
        for i in 0..nlev {
            let si: f64 = op[i].iter().sum::<f64>() / l as f64;
            bin_op_sum[bin][i] += si;
            for j in 0..nlev {
                for tau in 0..=tau_max {
                    let mut acc = 0.0;
                    for t in 0..l {
                        acc += op[i][t] * op[j][(t + tau) % l];
                    }
                    bin_corr_sum[bin][i][j][tau] += acc / l as f64;
                }
            }
        }
        // E (2++) channel accumulation -- same shape, sized 2*nlev.
        for i in 0..n_e {
            let si: f64 = op_e[i].iter().sum::<f64>() / l as f64;
            bin_op_E_sum[bin][i] += si;
            for j in 0..n_e {
                for tau in 0..=tau_max {
                    let mut acc = 0.0;
                    for t in 0..l {
                        acc += op_e[i][t] * op_e[j][(t + tau) % l];
                    }
                    bin_corr_E_sum[bin][i][j][tau] += acc / l as f64;
                }
            }
        }
        n_collected += 1;
    }

    // Global connected correlators (A_1 and E), rebuilt from the bin sums.
    let nc = n_collected.max(1) as f64;
    let mut mean_op = vec![0.0f64; nlev];
    let mut corr = vec![vec![vec![0.0f64; tau_max + 1]; nlev]; nlev];
    for b in 0..n_bins {
        for i in 0..nlev {
            mean_op[i] += bin_op_sum[b][i];
            for j in 0..nlev {
                for tau in 0..=tau_max {
                    corr[i][j][tau] += bin_corr_sum[b][i][j][tau];
                }
            }
        }
    }
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

    let mut mean_op_E = vec![0.0f64; n_e];
    let mut corr_E = vec![vec![vec![0.0f64; tau_max + 1]; n_e]; n_e];
    for b in 0..n_bins {
        for i in 0..n_e {
            mean_op_E[i] += bin_op_E_sum[b][i];
            for j in 0..n_e {
                for tau in 0..=tau_max {
                    corr_E[i][j][tau] += bin_corr_E_sum[b][i][j][tau];
                }
            }
        }
    }
    for i in 0..n_e {
        mean_op_E[i] /= nc;
    }
    for i in 0..n_e {
        for j in 0..n_e {
            for tau in 0..=tau_max {
                corr_E[i][j][tau] = corr_E[i][j][tau] / nc - mean_op_E[i] * mean_op_E[j];
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
        n_bins,
        bin_counts,
        bin_op_sum,
        bin_corr_sum,
        mean_op_E,
        corr_E,
        bin_op_E_sum,
        bin_corr_E_sum,
    }
}

// ---------------------------------------------------------------------------
// String tension: rectangular Wilson loops W(R,T) in the (spatial, time)
// planes, with APE-smeared spatial links to improve the static-potential
// signal.  Python extracts sigma via Creutz ratios / the static potential.
// ---------------------------------------------------------------------------

impl Lattice {
    /// Site reached by `n` steps in +/-mu from `site` (periodic).
    #[inline]
    fn shift_n(&self, mut site: usize, mu: usize, n: usize, fwd: bool) -> usize {
        for _ in 0..n {
            site = self.shift(site, mu, fwd);
        }
        site
    }
}

pub struct StringTensionData {
    pub l: usize,
    pub beta: f64,
    pub n_therm: usize,
    pub n_collected: usize,
    pub overrelax: usize,
    pub threads: usize,
    pub r_max: usize,
    pub t_max: usize,
    pub smear_steps: usize,
    pub smear_alpha: f64,
    /// `w[r-1][t-1] = <W(r, t)>`, the planar R x T Wilson loop (R spatial,
    /// T temporal), averaged over sites and the 3 spatial directions.
    pub w: Vec<Vec<f64>>,
    /// Number of (contiguous) configuration bins for jackknife error analysis.
    pub n_bins: usize,
    /// Configs in each bin; `[n_bins]`.
    pub bin_counts: Vec<usize>,
    /// Per-bin Wilson-loop sum: sum over the bin's configs of the per-config
    /// loop `(1/(vol*(DIM-1))) sum_{sites,dirs} W(r,t)`.  `[n_bins][r][t]`.
    /// The leave-one-out grid is `(sum_b - bin_b) / (n_collected - count_b)`.
    pub bin_w_sum: Vec<Vec<Vec<f64>>>,
}

/// Measure rectangular Wilson loops W(R,T) for R=1..=r_max, T=1..=t_max.
/// Spatial segments use spatial links APE-smeared `smear_steps` times;
/// temporal segments use the unsmeared temporal links.
#[allow(clippy::too_many_arguments)]
pub fn measure_string_tension(
    l: usize,
    beta: f64,
    n_therm: usize,
    n_meas: usize,
    meas_interval: usize,
    n_overrelax: usize,
    r_max: usize,
    t_max: usize,
    smear_steps: usize,
    smear_alpha: f64,
    n_bins: usize,
    seed: u64,
    threads: usize,
) -> StringTensionData {
    assert!(r_max < l && t_max < l, "loop extents must be < L");
    let mut lat = Lattice::new_hot(l, seed);
    let classes = build_classes(&lat);
    let mut sweep_idx: u64 = 0;
    for _ in 0..n_therm {
        sweep(&mut lat, beta, n_overrelax, sweep_idx, seed, threads, &classes);
        sweep_idx += 1;
    }

    let vol = lat.vol;
    // Contiguous binning of the collected configs for jackknife errors (same
    // convention as measure_glueball): clamp the bin count to the expected
    // collected count and assign by collection index.
    let expected = (n_meas / meas_interval.max(1)).max(1);
    let n_bins = n_bins.clamp(1, expected);
    let bin_size = (expected + n_bins - 1) / n_bins;
    let mut bin_counts = vec![0usize; n_bins];
    let mut bin_w_sum = vec![vec![vec![0.0f64; t_max]; r_max]; n_bins];
    let dirnorm = (vol * (DIM - 1)) as f64;
    let mut n_collected = 0usize;
    let mut since = 0usize;

    for _ in 0..n_meas {
        sweep(&mut lat, beta, n_overrelax, sweep_idx, seed, threads, &classes);
        sweep_idx += 1;
        since += 1;
        if since < meas_interval {
            continue;
        }
        since = 0;

        // APE-smear spatial links.
        let mut sm = lat.links.clone();
        for _ in 0..smear_steps {
            sm = ape_smear_spatial(&sm, &lat, smear_alpha, threads);
        }

        // Temporal lines tl[t][x] = product of t temporal links from x (unsmeared).
        let mut tl = vec![vec![ID; vol]; t_max + 1];
        for x in 0..vol {
            tl[1][x] = lat.link(x, 0);
        }
        for t in 2..=t_max {
            for x in 0..vol {
                let xp = lat.shift_n(x, 0, t - 1, true);
                tl[t][x] = mul(tl[t - 1][x], lat.link(xp, 0));
            }
        }

        // Per spatial direction: spatial lines (smeared) + loop assembly.
        let mut w_cfg = vec![vec![0.0f64; t_max]; r_max];
        for i in 1..DIM {
            let mut sl = vec![vec![ID; vol]; r_max + 1];
            for x in 0..vol {
                sl[1][x] = lget(&sm, x, i);
            }
            for r in 2..=r_max {
                for x in 0..vol {
                    let xp = lat.shift_n(x, i, r - 1, true);
                    sl[r][x] = mul(sl[r - 1][x], lget(&sm, xp, i));
                }
            }
            // Parallel loop assembly: each thread accumulates a partial w over a
            // contiguous site range; combine after.  (Statistical observable, so
            // float-sum reordering across threads is immaterial.)
            let sl_ref = &sl;
            let tl_ref = &tl;
            let lat_ref = &lat;
            let nthreads = threads.max(1).min(vol);
            let chunk = (vol + nthreads - 1) / nthreads;
            let partials: Vec<Vec<Vec<f64>>> = std::thread::scope(|s| {
                let handles: Vec<_> = (0..nthreads)
                    .map(|ti| {
                        let lo = ti * chunk;
                        let hi = ((ti + 1) * chunk).min(vol);
                        s.spawn(move || {
                            let mut wp = vec![vec![0.0f64; t_max]; r_max];
                            for x in lo..hi {
                                for r in 1..=r_max {
                                    let x_pr = lat_ref.shift_n(x, i, r, true);
                                    for t in 1..=t_max {
                                        let x_pt = lat_ref.shift_n(x, 0, t, true);
                                        let lp = mul(
                                            mul(sl_ref[r][x], tl_ref[t][x_pr]),
                                            mul(dag(sl_ref[r][x_pt]), dag(tl_ref[t][x])),
                                        );
                                        wp[r - 1][t - 1] += lp[0];
                                    }
                                }
                            }
                            wp
                        })
                    })
                    .collect();
                handles.into_iter().map(|h| h.join().unwrap()).collect()
            });
            for wp in partials {
                for r in 0..r_max {
                    for t in 0..t_max {
                        w_cfg[r][t] += wp[r][t];
                    }
                }
            }
        }
        // Bin this config's per-config loop average (normalized over sites and
        // the DIM-1 spatial directions).
        let bin = (n_collected / bin_size).min(n_bins - 1);
        bin_counts[bin] += 1;
        for r in 0..r_max {
            for t in 0..t_max {
                bin_w_sum[bin][r][t] += w_cfg[r][t] / dirnorm;
            }
        }
        n_collected += 1;
    }

    // Global grid rebuilt from the bin sums: w[r][t] = (sum_b bin_w_sum) / nc.
    let nc = n_collected.max(1) as f64;
    let mut w = vec![vec![0.0f64; t_max]; r_max];
    for b in 0..n_bins {
        for r in 0..r_max {
            for t in 0..t_max {
                w[r][t] += bin_w_sum[b][r][t];
            }
        }
    }
    for r in 0..r_max {
        for t in 0..t_max {
            w[r][t] /= nc;
        }
    }

    StringTensionData {
        l,
        beta,
        n_therm,
        n_collected,
        overrelax: n_overrelax,
        threads,
        r_max,
        t_max,
        smear_steps,
        smear_alpha,
        w,
        n_bins,
        bin_counts,
        bin_w_sum,
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
        let g = measure_glueball(8, 2.4, 300, 2000, 4, 4, &[0, 4, 8], 0.5, 8, 7, 4);
        let top = g.smear_levels.len() - 1;
        let c = &g.corr[top][top];
        assert!(c[0] > 0.0, "C(0) must be positive, got {}", c[0]);
        assert!(c[0] > c[1], "C(0) should exceed C(1): {} vs {}", c[0], c[1]);
        let meff = (c[0] / c[1]).ln();
        assert!(meff > 0.0 && meff.is_finite(), "effective mass should be positive finite, got {meff}");

        // Bin bookkeeping: counts sum to n_collected, and the global connected
        // correlator equals the one rebuilt from the bin sums (the jackknife
        // inputs must reproduce the reported central value).
        assert_eq!(g.bin_counts.iter().sum::<usize>(), g.n_collected);
        let nc = g.n_collected as f64;
        let mut acc = 0.0;
        let mut mop_i = 0.0;
        for b in 0..g.n_bins {
            acc += g.bin_corr_sum[b][top][top][0];
            mop_i += g.bin_op_sum[b][top];
        }
        let rebuilt = acc / nc - (mop_i / nc) * (mop_i / nc);
        assert!((rebuilt - c[0]).abs() < 1e-9 * c[0].abs().max(1.0),
            "bin-rebuilt C(0)={rebuilt} must match reported {}", c[0]);
    }

    #[test]
    fn glueball_2pp_E_channel_sane() {
        // 2++ E-channel correlator: 2 operators per smear level, diagonal at
        // tau=0 must be non-negative (it is Var(O_E) >= 0), and the global
        // correlator must be reproducible from the bin sums.
        let g = measure_glueball(8, 2.4, 300, 2000, 4, 4, &[0, 4, 8], 0.5, 8, 7, 4);
        let nlev = g.smear_levels.len();
        let n_e = 2 * nlev;
        assert_eq!(g.mean_op_E.len(), n_e, "E-channel must have 2*nlev operators");
        assert_eq!(g.corr_E.len(), n_e);

        // Diagonal Var(O_E_a) >= 0 for every (smear, component).
        for a in 0..n_e {
            let c0 = g.corr_E[a][a][0];
            assert!(c0 >= -1e-9, "C^E_{a}{a}(0)={c0} must be >= 0 (Var)");
        }

        // Bin reconstruction matches the reported global E correlator at tau=0.
        let nc = g.n_collected as f64;
        let top_e = n_e - 1; // last E operator (most-smeared, E_2)
        let mut acc = 0.0;
        let mut mop_e = 0.0;
        for b in 0..g.n_bins {
            acc += g.bin_corr_E_sum[b][top_e][top_e][0];
            mop_e += g.bin_op_E_sum[b][top_e];
        }
        let rebuilt = acc / nc - (mop_e / nc) * (mop_e / nc);
        let reported = g.corr_E[top_e][top_e][0];
        assert!((rebuilt - reported).abs() < 1e-9 * reported.abs().max(1.0),
            "bin-rebuilt C^E({top_e},{top_e})(0)={rebuilt} must match reported {reported}");
    }

    #[test]
    fn wilson_loops_decrease_and_creutz_positive() {
        // W(R,T) must decrease with area; the Creutz ratio must be positive
        // (a positive string tension).
        let s = measure_string_tension(8, 2.4, 300, 2000, 4, 4, 3, 3, 0, 0.5, 4, 11, 4);
        let w = &s.w; // w[r-1][t-1]
        assert!(w[0][0] > w[1][0], "W(2,1) should be < W(1,1)");
        assert!(w[0][0] > w[0][1], "W(1,2) should be < W(1,1)");
        assert!(w[2][2] > 0.0, "W(3,3) should still have positive signal");
        // Creutz ratio chi(2,2) = -ln[ W(2,2)W(1,1) / (W(1,2)W(2,1)) ] > 0.
        let chi = -(w[1][1] * w[0][0] / (w[0][1] * w[1][0])).ln();
        assert!(chi > 0.0, "Creutz ratio chi(2,2) should be positive, got {chi}");

        // Bin bookkeeping: counts sum to n_collected, and the global grid equals
        // the one rebuilt from the bin sums (jackknife inputs reproduce <W>).
        assert_eq!(s.bin_counts.iter().sum::<usize>(), s.n_collected);
        let nc = s.n_collected as f64;
        let mut rebuilt = 0.0;
        for b in 0..s.n_bins {
            rebuilt += s.bin_w_sum[b][1][1];
        }
        rebuilt /= nc;
        assert!((rebuilt - w[1][1]).abs() < 1e-9, "rebuilt W(2,2) {rebuilt} != {}", w[1][1]);
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
