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
unsafe fn staple_ptr(base: *const Su2, nb: &Neighbors, site: usize, mu: usize) -> Su2 {
    #[inline(always)]
    unsafe fn get(base: *const Su2, s: usize, m: usize) -> Su2 {
        *base.add(s * DIM + m)
    }
    let x_pmu = nb.fwd(site, mu); // invariant of nu; hoisted out of the loop
    let mut a = [0.0; 4];
    for nu in 0..DIM {
        if nu == mu {
            continue;
        }
        let x_pnu = nb.fwd(site, nu);
        let fwd = mul(
            mul(get(base, x_pmu, nu), dag(get(base, x_pnu, mu))),
            dag(get(base, site, nu)),
        );
        let x_mnu = nb.bwd(site, nu);
        let x_mnu_pmu = nb.fwd(x_mnu, mu);
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
// Precomputed periodic neighbour table.  Every hot path (sweep staples, APE
// smearing, glueball/Wilson-loop measurement) walks the lattice by `+/-mu`
// hops; doing the `coord()` divide/modulo per hop dominated the index
// arithmetic.  Build the `site -> neighbour` map once and read it O(1).
//
// `fwd`/`bwd` are flat `[site*DIM + mu]` arrays (same indexing as `links`), so
// the access pattern matches the link buffer.  `Neighbors` owns its data and
// borrows nothing, so it is `Sync` and can be shared `&` into worker threads.
// ---------------------------------------------------------------------------

pub struct Neighbors {
    pub l: usize,
    pub vol: usize,
    fwd: Vec<usize>, // fwd[site*DIM + mu] = site shifted +1 in direction mu
    bwd: Vec<usize>, // bwd[site*DIM + mu] = site shifted -1 in direction mu
}

impl Neighbors {
    pub fn new(geom: &Geom) -> Self {
        let vol = geom.vol;
        let mut fwd = vec![0usize; vol * DIM];
        let mut bwd = vec![0usize; vol * DIM];
        for site in 0..vol {
            for mu in 0..DIM {
                fwd[site * DIM + mu] = geom.shift(site, mu, true);
                bwd[site * DIM + mu] = geom.shift(site, mu, false);
            }
        }
        Neighbors { l: geom.l, vol, fwd, bwd }
    }

    #[inline(always)]
    pub fn fwd(&self, site: usize, mu: usize) -> usize {
        self.fwd[site * DIM + mu]
    }
    #[inline(always)]
    pub fn bwd(&self, site: usize, mu: usize) -> usize {
        self.bwd[site * DIM + mu]
    }
    #[inline(always)]
    pub fn shift(&self, site: usize, mu: usize, fwd: bool) -> usize {
        if fwd {
            self.fwd(site, mu)
        } else {
            self.bwd(site, mu)
        }
    }
    /// `n` hops in +/-mu (periodic).  Each hop is now an O(1) table read.
    #[inline]
    pub fn shift_n(&self, mut site: usize, mu: usize, n: usize, fwd: bool) -> usize {
        for _ in 0..n {
            site = self.shift(site, mu, fwd);
        }
        site
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
    nb: &Neighbors,
    link_idx: usize,
    beta: f64,
    is_heatbath: bool,
    sweep_idx: u64,
    pass_tag: u64,
    seed: u64,
) {
    let site = link_idx / DIM;
    let mu = link_idx % DIM;
    let a = staple_ptr(base, nb, site, mu);
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
    nb: &Neighbors,
) {
    let nthreads = threads.max(1);

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
                                base, nb, link_idx, beta, is_heatbath, sweep_idx, pass_tag,
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
            let nb = nb;
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
                                        base, nb, link_idx, beta, is_heatbath, sweep_idx,
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
    let nb = Neighbors::new(&lat.geom());
    let mut sweep_idx: u64 = 0;
    for _ in 0..n_therm {
        sweep(&mut lat, beta, n_overrelax, sweep_idx, seed, threads, &classes, &nb);
        sweep_idx += 1;
    }
    let mut samples: Vec<f64> = Vec::new();
    let mut since = 0usize;
    for _ in 0..n_meas {
        sweep(&mut lat, beta, n_overrelax, sweep_idx, seed, threads, &classes, &nb);
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
fn spatial_staple_from(links: &[Su2], nb: &Neighbors, site: usize, mu: usize) -> Su2 {
    let x_pmu = nb.fwd(site, mu); // invariant of nu
    let mut a = [0.0; 4];
    for nu in 1..DIM {
        if nu == mu {
            continue;
        }
        let x_pnu = nb.fwd(site, nu);
        let fwd = mul(
            mul(lget(links, x_pmu, nu), dag(lget(links, x_pnu, mu))),
            dag(lget(links, site, nu)),
        );
        let x_mnu = nb.bwd(site, nu);
        let x_mnu_pmu = nb.fwd(x_mnu, mu);
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
fn ape_smear_spatial(links: &[Su2], nb: &Neighbors, alpha: f64, threads: usize) -> Vec<Su2> {
    let mut out = links.to_vec();
    let vol = nb.vol;
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
                        let st = spatial_staple_from(links, nb, site, mu);
                        out_chunk[j * DIM + mu] =
                            renorm(add(lget(links, site, mu), scale(st, alpha)));
                    }
                }
            });
        }
    });
    out
}

/// Reusable-buffer variant of `ape_smear_spatial`: writes one APE step from
/// `src` into `dst` (must be pre-sized to `src.len()`), avoiding the per-call
/// `Vec` allocation in the measurement hot loop.
fn ape_smear_spatial_into(src: &[Su2], dst: &mut [Su2], nb: &Neighbors, alpha: f64, threads: usize) {
    dst.copy_from_slice(src); // temporal links pass through unchanged
    let vol = nb.vol;
    let nthreads = threads.max(1).min(vol);
    let chunk_sites = (vol + nthreads - 1) / nthreads;
    std::thread::scope(|s| {
        for (ci, out_chunk) in dst.chunks_mut(chunk_sites * DIM).enumerate() {
            let site0 = ci * chunk_sites;
            s.spawn(move || {
                let n = out_chunk.len() / DIM;
                for j in 0..n {
                    let site = site0 + j;
                    for mu in 1..DIM {
                        let st = spatial_staple_from(src, nb, site, mu);
                        out_chunk[j * DIM + mu] =
                            renorm(add(lget(src, site, mu), scale(st, alpha)));
                    }
                }
            });
        }
    });
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
fn timeslice_op_planes(links: &[Su2], nb: &Neighbors, t: usize) -> [f64; 3] {
    let mut p = [0.0f64; 3];
    let st0 = nb.l * nb.l * nb.l; // stride for x0
    let base = t * st0;
    for s in 0..st0 {
        let site = base + s; // sites with coord(.,0) == t (x0 is the slowest index)
        let mut k = 0usize;
        for i in 1..DIM {
            for j in (i + 1)..DIM {
                let x_pi = nb.fwd(site, i);
                let x_pj = nb.fwd(site, j);
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
    let nb = Neighbors::new(&lat.geom());
    let mut sweep_idx: u64 = 0;
    for _ in 0..n_therm {
        sweep(&mut lat, beta, n_overrelax, sweep_idx, seed, threads, &classes, &nb);
        sweep_idx += 1;
    }

    let mut n_collected = 0usize;
    let mut since = 0usize;

    for _ in 0..n_meas {
        sweep(&mut lat, beta, n_overrelax, sweep_idx, seed, threads, &classes, &nb);
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
                let nb_ref = &nb;
                let nthreads = threads.max(1).min(l);
                let chunk = (l + nthreads - 1) / nthreads;
                std::thread::scope(|s| {
                    for (ci, rchunk) in row.chunks_mut(chunk).enumerate() {
                        let t0 = ci * chunk;
                        s.spawn(move || {
                            for (j, slot) in rchunk.iter_mut().enumerate() {
                                *slot = timeslice_op_planes(sm_ref, nb_ref, t0 + j);
                            }
                        });
                    }
                });
                idx += 1;
            }
            if level < max_level {
                sm = ape_smear_spatial(&sm, &nb, smear_alpha, threads);
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
    let nb = Neighbors::new(&lat.geom());
    let mut sweep_idx: u64 = 0;
    for _ in 0..n_therm {
        sweep(&mut lat, beta, n_overrelax, sweep_idx, seed, threads, &classes, &nb);
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
        sweep(&mut lat, beta, n_overrelax, sweep_idx, seed, threads, &classes, &nb);
        sweep_idx += 1;
        since += 1;
        if since < meas_interval {
            continue;
        }
        since = 0;

        // APE-smear spatial links.
        let mut sm = lat.links.clone();
        for _ in 0..smear_steps {
            sm = ape_smear_spatial(&sm, &nb, smear_alpha, threads);
        }

        // Temporal lines tl[t][x] = product of t temporal links from x (unsmeared).
        let mut tl = vec![vec![ID; vol]; t_max + 1];
        for x in 0..vol {
            tl[1][x] = lat.link(x, 0);
        }
        for t in 2..=t_max {
            for x in 0..vol {
                let xp = nb.shift_n(x, 0, t - 1, true);
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
                    let xp = nb.shift_n(x, i, r - 1, true);
                    sl[r][x] = mul(sl[r - 1][x], lget(&sm, xp, i));
                }
            }
            // Parallel loop assembly: each thread accumulates a partial w over a
            // contiguous site range; combine after.  (Statistical observable, so
            // float-sum reordering across threads is immaterial.)
            let sl_ref = &sl;
            let tl_ref = &tl;
            let nb_ref = &nb;
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
                                    let x_pr = nb_ref.shift_n(x, i, r, true);
                                    for t in 1..=t_max {
                                        let x_pt = nb_ref.shift_n(x, 0, t, true);
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
// Combined single-chain measurement: glueball (0++/2++) operators AND Wilson
// loops on the SAME Markov chain, with checkpoint/resume.  One thermalization
// and one sweep stream feed both observables, instead of two independent
// chains (≈30% fewer sweeps, half the thermalization).  Buffers are hoisted
// out of the per-config loop so the measurement allocates nothing steady-state.
//
// Sharding: run K of these with distinct seeds on separate machines, each
// covering n_meas/K sweeps; the Python `merge_shards` tool concatenates their
// configuration bins (independent draws -> a valid larger jackknife ensemble).
// ---------------------------------------------------------------------------

#[derive(Clone)]
pub struct CombinedParams {
    pub l: usize,
    pub beta: f64,
    pub n_therm: usize,
    /// Number of sweeps in the measurement phase; a config is collected every
    /// `meas_interval` sweeps, so the run yields `n_meas / meas_interval` configs.
    pub n_meas: usize,
    pub meas_interval: usize,
    pub n_overrelax: usize,
    pub smear_levels: Vec<usize>,
    pub smear_alpha: f64,
    pub r_max: usize,
    pub t_max: usize,
    /// APE smear steps applied to the spatial links for the Wilson-loop (sigma)
    /// measurement.  Captured for free from the glueball smear ladder when
    /// `sigma_smear <= max(smear_levels)`.
    pub sigma_smear: usize,
    pub n_bins: usize,
    pub seed: u64,
    pub threads: usize,
}

impl CombinedParams {
    /// Configuration-bin signature; a checkpoint is only resumed if it matches,
    /// so a changed run config never silently continues from a stale chain.
    fn signature(&self) -> u64 {
        let mut h = splitmix(0xC0FFEE_u64 ^ self.l as u64);
        for v in [
            self.beta.to_bits(),
            self.n_therm as u64,
            self.n_meas as u64,
            self.meas_interval as u64,
            self.n_overrelax as u64,
            self.smear_alpha.to_bits(),
            self.r_max as u64,
            self.t_max as u64,
            self.sigma_smear as u64,
            self.n_bins as u64,
            self.seed as u64,
        ] {
            h = splitmix(h ^ v);
        }
        for &s in &self.smear_levels {
            h = splitmix(h ^ s as u64);
        }
        h
    }

    fn expected_configs(&self) -> usize {
        (self.n_meas / self.meas_interval.max(1)).max(1)
    }
}

/// The mutable accumulators + chain position that fully define a resumable run.
struct ChainState {
    stage: u8, // 0 = thermalizing, 1 = measuring
    therm_done: usize,
    meas_sweeps_done: usize,
    n_collected: usize,
    since: usize,
    sweep_idx: u64,
    elapsed: f64,
    links: Vec<Su2>,
    bin_counts: Vec<usize>,             // shared binning (same configs feed both)
    g_op: Vec<Vec<f64>>,                // [n_bins][nlev]            0++ operator sums
    g_corr: Vec<Vec<Vec<Vec<f64>>>>,    // [n_bins][nlev][nlev][tau] 0++ correlator sums
    g_op_e: Vec<Vec<f64>>,              // [n_bins][n_e]             2++ operator sums
    g_corr_e: Vec<Vec<Vec<Vec<f64>>>>,  // [n_bins][n_e][n_e][tau]   2++ correlator sums
    s_w: Vec<Vec<Vec<f64>>>,            // [n_bins][r_max][t_max]    Wilson-loop sums
}

impl ChainState {
    fn fresh(p: &CombinedParams) -> Self {
        let nlev = p.smear_levels.len();
        let n_e = 2 * nlev;
        let tau_max = p.l / 2;
        let nb = p.n_bins;
        ChainState {
            stage: 0,
            therm_done: 0,
            meas_sweeps_done: 0,
            n_collected: 0,
            since: 0,
            sweep_idx: 0,
            elapsed: 0.0,
            links: Vec::new(), // filled by the caller from the hot lattice
            bin_counts: vec![0usize; nb],
            g_op: vec![vec![0.0; nlev]; nb],
            g_corr: vec![vec![vec![vec![0.0; tau_max + 1]; nlev]; nlev]; nb],
            g_op_e: vec![vec![0.0; n_e]; nb],
            g_corr_e: vec![vec![vec![vec![0.0; tau_max + 1]; n_e]; n_e]; nb],
            s_w: vec![vec![vec![0.0; p.t_max]; p.r_max]; nb],
        }
    }
}

// --- binary checkpoint serialization (little-endian, std-only) --------------

const CKPT_MAGIC: u64 = 0x59_4D_43_4B_50_54_30_32; // "YMCKPT02"

fn pu64(b: &mut Vec<u8>, x: u64) {
    b.extend_from_slice(&x.to_le_bytes());
}
fn pf64(b: &mut Vec<u8>, x: f64) {
    b.extend_from_slice(&x.to_bits().to_le_bytes());
}
fn pf64s(b: &mut Vec<u8>, v: &[f64]) {
    for &x in v {
        pf64(b, x);
    }
}

struct Cur<'a> {
    b: &'a [u8],
    i: usize,
}
impl<'a> Cur<'a> {
    fn gu64(&mut self) -> u64 {
        let v = u64::from_le_bytes(self.b[self.i..self.i + 8].try_into().unwrap());
        self.i += 8;
        v
    }
    fn gf64(&mut self) -> f64 {
        f64::from_bits(self.gu64())
    }
    fn gf64s(&mut self, out: &mut [f64]) {
        for x in out.iter_mut() {
            *x = self.gf64();
        }
    }
}

/// Atomically write the checkpoint: serialize to `<path>.tmp`, then rename over
/// `path` (rename is atomic on local FS and on gcsfuse), so a crash mid-write
/// never corrupts a resumable checkpoint.
fn save_checkpoint(path: &str, sig: u64, st: &ChainState) -> std::io::Result<()> {
    let mut b = Vec::with_capacity(st.links.len() * 32 + 4096);
    pu64(&mut b, CKPT_MAGIC);
    pu64(&mut b, sig);
    pu64(&mut b, st.stage as u64);
    pu64(&mut b, st.therm_done as u64);
    pu64(&mut b, st.meas_sweeps_done as u64);
    pu64(&mut b, st.n_collected as u64);
    pu64(&mut b, st.since as u64);
    pu64(&mut b, st.sweep_idx);
    pf64(&mut b, st.elapsed);
    pu64(&mut b, st.links.len() as u64);
    for u in &st.links {
        pf64s(&mut b, u);
    }
    for &c in &st.bin_counts {
        pu64(&mut b, c as u64);
    }
    for row in &st.g_op {
        pf64s(&mut b, row);
    }
    for mat in &st.g_corr {
        for r in mat {
            for s in r {
                pf64s(&mut b, s);
            }
        }
    }
    for row in &st.g_op_e {
        pf64s(&mut b, row);
    }
    for mat in &st.g_corr_e {
        for r in mat {
            for s in r {
                pf64s(&mut b, s);
            }
        }
    }
    for mat in &st.s_w {
        for r in mat {
            pf64s(&mut b, r);
        }
    }
    let tmp = format!("{path}.tmp");
    std::fs::write(&tmp, &b)?;
    std::fs::rename(&tmp, path)
}

/// Load a checkpoint if it exists and matches `sig` and the param-derived
/// shapes; otherwise `None` (caller starts a fresh chain).  Shapes are rebuilt
/// from `p` so a truncated/mismatched file is rejected rather than misread.
fn load_checkpoint(path: &str, sig: u64, p: &CombinedParams) -> Option<ChainState> {
    let bytes = std::fs::read(path).ok()?;
    if bytes.len() < 16 {
        return None;
    }
    let mut c = Cur { b: &bytes, i: 0 };
    if c.gu64() != CKPT_MAGIC || c.gu64() != sig {
        eprintln!("  [ckpt] {path}: magic/signature mismatch -> ignoring, starting fresh");
        return None;
    }
    let mut st = ChainState::fresh(p);
    st.stage = c.gu64() as u8;
    st.therm_done = c.gu64() as usize;
    st.meas_sweeps_done = c.gu64() as usize;
    st.n_collected = c.gu64() as usize;
    st.since = c.gu64() as usize;
    st.sweep_idx = c.gu64();
    st.elapsed = c.gf64();
    let nlinks = c.gu64() as usize;
    // Guard against a truncated file before we start indexing.
    let nlev = p.smear_levels.len();
    let n_e = 2 * nlev;
    let tau_max = p.l / 2;
    let nb = p.n_bins;
    let need = 9 * 8
        + 8
        + nlinks * 32
        + nb * 8
        + nb * nlev * 8
        + nb * nlev * nlev * (tau_max + 1) * 8
        + nb * n_e * 8
        + nb * n_e * n_e * (tau_max + 1) * 8
        + nb * p.r_max * p.t_max * 8;
    if bytes.len() < need || nlinks != p.l.pow(DIM as u32) * DIM {
        eprintln!("  [ckpt] {path}: size/shape mismatch -> ignoring, starting fresh");
        return None;
    }
    st.links = vec![ID; nlinks];
    for u in st.links.iter_mut() {
        c.gf64s(u);
    }
    for x in st.bin_counts.iter_mut() {
        *x = c.gu64() as usize;
    }
    for row in st.g_op.iter_mut() {
        c.gf64s(row);
    }
    for mat in st.g_corr.iter_mut() {
        for r in mat.iter_mut() {
            for s in r.iter_mut() {
                c.gf64s(s);
            }
        }
    }
    for row in st.g_op_e.iter_mut() {
        c.gf64s(row);
    }
    for mat in st.g_corr_e.iter_mut() {
        for r in mat.iter_mut() {
            for s in r.iter_mut() {
                c.gf64s(s);
            }
        }
    }
    for mat in st.s_w.iter_mut() {
        for r in mat.iter_mut() {
            c.gf64s(r);
        }
    }
    Some(st)
}

// --- finalize accumulators -> the existing public result structs ------------

fn finalize_glueball(p: &CombinedParams, st: &ChainState) -> GlueballData {
    let nlev = p.smear_levels.len();
    let n_e = 2 * nlev;
    let tau_max = p.l / 2;
    let nc = st.n_collected.max(1) as f64;

    let mut mean_op = vec![0.0; nlev];
    let mut corr = vec![vec![vec![0.0; tau_max + 1]; nlev]; nlev];
    for b in 0..p.n_bins {
        for i in 0..nlev {
            mean_op[i] += st.g_op[b][i];
            for j in 0..nlev {
                for tau in 0..=tau_max {
                    corr[i][j][tau] += st.g_corr[b][i][j][tau];
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

    let mut mean_op_e = vec![0.0; n_e];
    let mut corr_e = vec![vec![vec![0.0; tau_max + 1]; n_e]; n_e];
    for b in 0..p.n_bins {
        for i in 0..n_e {
            mean_op_e[i] += st.g_op_e[b][i];
            for j in 0..n_e {
                for tau in 0..=tau_max {
                    corr_e[i][j][tau] += st.g_corr_e[b][i][j][tau];
                }
            }
        }
    }
    for i in 0..n_e {
        mean_op_e[i] /= nc;
    }
    for i in 0..n_e {
        for j in 0..n_e {
            for tau in 0..=tau_max {
                corr_e[i][j][tau] = corr_e[i][j][tau] / nc - mean_op_e[i] * mean_op_e[j];
            }
        }
    }

    GlueballData {
        l: p.l,
        beta: p.beta,
        n_therm: p.n_therm,
        n_collected: st.n_collected,
        smear_levels: p.smear_levels.clone(),
        smear_alpha: p.smear_alpha,
        overrelax: p.n_overrelax,
        threads: p.threads,
        mean_op,
        corr,
        n_bins: p.n_bins,
        bin_counts: st.bin_counts.clone(),
        bin_op_sum: st.g_op.clone(),
        bin_corr_sum: st.g_corr.clone(),
        mean_op_E: mean_op_e,
        corr_E: corr_e,
        bin_op_E_sum: st.g_op_e.clone(),
        bin_corr_E_sum: st.g_corr_e.clone(),
    }
}

fn finalize_sigma(p: &CombinedParams, st: &ChainState) -> StringTensionData {
    let nc = st.n_collected.max(1) as f64;
    let mut w = vec![vec![0.0; p.t_max]; p.r_max];
    for b in 0..p.n_bins {
        for r in 0..p.r_max {
            for t in 0..p.t_max {
                w[r][t] += st.s_w[b][r][t];
            }
        }
    }
    for r in 0..p.r_max {
        for t in 0..p.t_max {
            w[r][t] /= nc;
        }
    }
    StringTensionData {
        l: p.l,
        beta: p.beta,
        n_therm: p.n_therm,
        n_collected: st.n_collected,
        overrelax: p.n_overrelax,
        threads: p.threads,
        r_max: p.r_max,
        t_max: p.t_max,
        smear_steps: p.sigma_smear,
        smear_alpha: p.smear_alpha,
        w,
        n_bins: p.n_bins,
        bin_counts: st.bin_counts.clone(),
        bin_w_sum: st.s_w.clone(),
    }
}

/// Run (or resume) one combined chain.  Measures the 0++/2++ glueball operators
/// and the Wilson-loop grid on every collected config.
///
/// Checkpointing: if `ckpt_path` is set, the run resumes from it when present
/// and writes it every `ckpt_every_configs` collected configs (and at most
/// every `ckpt_every_secs` wall seconds).  `max_collect > 0` stops cleanly
/// after that many configs (a checkpoint is written first), for time-boxed
/// budget runs and for resume testing.  `on_progress(&g, &s, elapsed)` fires at
/// each checkpoint with the partial results, so a run can be analyzed live.
///
/// Returns `(glueball, sigma, elapsed_seconds, finished)`; `finished` is false
/// iff the run stopped early on `max_collect` with configs still owed.
#[allow(clippy::too_many_arguments)]
pub fn measure_combined(
    p: &CombinedParams,
    ckpt_path: Option<&str>,
    ckpt_every_configs: usize,
    ckpt_every_secs: f64,
    max_collect: usize,
    mut on_progress: impl FnMut(&GlueballData, &StringTensionData, f64),
) -> (GlueballData, StringTensionData, f64, bool) {
    use std::time::Instant;

    let nlev = p.smear_levels.len();
    let n_e = 2 * nlev;
    let tau_max = p.l / 2;
    let max_level = *p.smear_levels.iter().max().unwrap_or(&0);
    let target = p.expected_configs();
    let bin_size = (target + p.n_bins - 1) / p.n_bins;
    let sig = p.signature();
    let threads = p.threads;

    let mut lat = Lattice::new_hot(p.l, p.seed);
    let classes = build_classes(&lat);
    let nb = Neighbors::new(&lat.geom());
    let vol = lat.vol;

    // Resume if a matching checkpoint exists.
    let mut st = match ckpt_path.and_then(|path| load_checkpoint(path, sig, p)) {
        Some(loaded) => {
            lat.links.copy_from_slice(&loaded.links);
            eprintln!(
                "  [ckpt] resumed: stage={} therm_done={} collected={}/{} sweep_idx={}",
                loaded.stage, loaded.therm_done, loaded.n_collected, target, loaded.sweep_idx
            );
            loaded
        }
        None => ChainState::fresh(p),
    };

    // Per-config buffers, hoisted out of the loop (1.5: no steady-state allocs).
    let mut sm_a = vec![ID; vol * DIM];
    let mut sm_b = vec![ID; vol * DIM];
    let mut sm_sigma = vec![ID; vol * DIM];
    let mut op_planes = vec![vec![[0.0f64; 3]; p.l]; nlev];
    let mut op = vec![vec![0.0f64; p.l]; nlev];
    let mut op_e = vec![vec![0.0f64; p.l]; n_e];
    let mut tl = vec![vec![ID; vol]; p.t_max + 1];
    let mut sl = vec![vec![ID; vol]; p.r_max + 1];
    let mut w_cfg = vec![vec![0.0f64; p.t_max]; p.r_max];

    let mut wall = Instant::now();
    let mut last_ckpt = Instant::now();
    let mut configs_since_ckpt = 0usize;

    let do_ckpt = |st: &mut ChainState,
                   links: &[Su2],
                   wall: &mut Instant,
                   on_progress: &mut dyn FnMut(&GlueballData, &StringTensionData, f64)| {
        st.elapsed += wall.elapsed().as_secs_f64();
        *wall = Instant::now();
        st.links.clear();
        st.links.extend_from_slice(links);
        if let Some(path) = ckpt_path {
            if let Err(e) = save_checkpoint(path, sig, st) {
                eprintln!("  [ckpt] WARN: write failed: {e}");
            }
        }
        if st.stage == 1 {
            let g = finalize_glueball(p, st);
            let s = finalize_sigma(p, st);
            on_progress(&g, &s, st.elapsed);
        }
    };

    // --- thermalization (resumable) ---
    while st.therm_done < p.n_therm {
        sweep(&mut lat, p.beta, p.n_overrelax, st.sweep_idx, p.seed, threads, &classes, &nb);
        st.sweep_idx += 1;
        st.therm_done += 1;
        let time_due = ckpt_every_secs > 0.0 && last_ckpt.elapsed().as_secs_f64() >= ckpt_every_secs;
        let count_due = ckpt_every_configs > 0
            && st.therm_done % (ckpt_every_configs * p.meas_interval).max(1) == 0;
        if ckpt_path.is_some() && (time_due || count_due) {
            do_ckpt(&mut st, &lat.links, &mut wall, &mut on_progress);
            last_ckpt = Instant::now();
        }
    }
    st.stage = 1;

    // --- measurement (resumable) ---
    while st.meas_sweeps_done < p.n_meas {
        sweep(&mut lat, p.beta, p.n_overrelax, st.sweep_idx, p.seed, threads, &classes, &nb);
        st.sweep_idx += 1;
        st.meas_sweeps_done += 1;
        st.since += 1;
        if st.since < p.meas_interval {
            continue;
        }
        st.since = 0;

        // ---- glueball operators: APE smear ladder, record at smear_levels ----
        sm_a.copy_from_slice(&lat.links);
        let mut src_is_a = true;
        let mut idx = 0usize;
        let mut sigma_captured = false;
        for level in 0..=max_level {
            {
                let cur: &[Su2] = if src_is_a { &sm_a } else { &sm_b };
                while idx < nlev && p.smear_levels[idx] == level {
                    let row = &mut op_planes[idx];
                    let nb_ref = &nb;
                    let nthreads = threads.max(1).min(p.l);
                    let chunk = (p.l + nthreads - 1) / nthreads;
                    std::thread::scope(|s| {
                        for (ci, rchunk) in row.chunks_mut(chunk).enumerate() {
                            let t0 = ci * chunk;
                            s.spawn(move || {
                                for (j, slot) in rchunk.iter_mut().enumerate() {
                                    *slot = timeslice_op_planes(cur, nb_ref, t0 + j);
                                }
                            });
                        }
                    });
                    idx += 1;
                }
                if level == p.sigma_smear {
                    sm_sigma.copy_from_slice(cur);
                    sigma_captured = true;
                }
            }
            if level < max_level {
                if src_is_a {
                    ape_smear_spatial_into(&sm_a, &mut sm_b, &nb, p.smear_alpha, threads);
                } else {
                    ape_smear_spatial_into(&sm_b, &mut sm_a, &nb, p.smear_alpha, threads);
                }
                src_is_a = !src_is_a;
            }
        }

        // Derive 0++ (A_1) and 2++ (E) operators from the per-plane sums.
        let inv_sqrt6 = 1.0 / 6.0f64.sqrt();
        let inv_sqrt2 = 1.0 / 2.0f64.sqrt();
        for i in 0..nlev {
            for t in 0..p.l {
                let pl = op_planes[i][t];
                op[i][t] = pl[0] + pl[1] + pl[2];
                op_e[2 * i][t] = inv_sqrt6 * (2.0 * pl[2] - pl[0] - pl[1]);
                op_e[2 * i + 1][t] = inv_sqrt2 * (pl[1] - pl[0]);
            }
        }

        let bin = (st.n_collected / bin_size).min(p.n_bins - 1);
        st.bin_counts[bin] += 1;
        for i in 0..nlev {
            st.g_op[bin][i] += op[i].iter().sum::<f64>() / p.l as f64;
            for j in 0..nlev {
                for tau in 0..=tau_max {
                    let mut acc = 0.0;
                    for t in 0..p.l {
                        acc += op[i][t] * op[j][(t + tau) % p.l];
                    }
                    st.g_corr[bin][i][j][tau] += acc / p.l as f64;
                }
            }
        }
        for i in 0..n_e {
            st.g_op_e[bin][i] += op_e[i].iter().sum::<f64>() / p.l as f64;
            for j in 0..n_e {
                for tau in 0..=tau_max {
                    let mut acc = 0.0;
                    for t in 0..p.l {
                        acc += op_e[i][t] * op_e[j][(t + tau) % p.l];
                    }
                    st.g_corr_e[bin][i][j][tau] += acc / p.l as f64;
                }
            }
        }

        // ---- Wilson loops on the sigma-smeared spatial links ----
        if !sigma_captured {
            // sigma_smear > max(smear_levels): smear separately from the config.
            sm_sigma.copy_from_slice(&lat.links);
            for _ in 0..p.sigma_smear {
                ape_smear_spatial_into(&sm_a, &mut sm_b, &nb, p.smear_alpha, threads);
                std::mem::swap(&mut sm_a, &mut sm_b);
                sm_sigma.copy_from_slice(&sm_a);
            }
        }
        // Temporal lines (unsmeared) from the hot lattice.
        for x in 0..vol {
            tl[1][x] = lat.link(x, 0);
        }
        for t in 2..=p.t_max {
            for x in 0..vol {
                let xp = nb.shift_n(x, 0, t - 1, true);
                tl[t][x] = mul(tl[t - 1][x], lat.link(xp, 0));
            }
        }
        for r in 0..p.r_max {
            for t in 0..p.t_max {
                w_cfg[r][t] = 0.0;
            }
        }
        for i in 1..DIM {
            for x in 0..vol {
                sl[1][x] = lget(&sm_sigma, x, i);
            }
            for r in 2..=p.r_max {
                for x in 0..vol {
                    let xp = nb.shift_n(x, i, r - 1, true);
                    sl[r][x] = mul(sl[r - 1][x], lget(&sm_sigma, xp, i));
                }
            }
            let sl_ref = &sl;
            let tl_ref = &tl;
            let nb_ref = &nb;
            let (r_max, t_max) = (p.r_max, p.t_max);
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
                                    let x_pr = nb_ref.shift_n(x, i, r, true);
                                    for t in 1..=t_max {
                                        let x_pt = nb_ref.shift_n(x, 0, t, true);
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
                for r in 0..p.r_max {
                    for t in 0..p.t_max {
                        w_cfg[r][t] += wp[r][t];
                    }
                }
            }
        }
        let dirnorm = (vol * (DIM - 1)) as f64;
        for r in 0..p.r_max {
            for t in 0..p.t_max {
                st.s_w[bin][r][t] += w_cfg[r][t] / dirnorm;
            }
        }

        st.n_collected += 1;
        configs_since_ckpt += 1;

        let time_due = ckpt_every_secs > 0.0 && last_ckpt.elapsed().as_secs_f64() >= ckpt_every_secs;
        let count_due = ckpt_every_configs > 0 && configs_since_ckpt >= ckpt_every_configs;
        let stop = max_collect > 0 && st.n_collected >= max_collect;
        if ckpt_path.is_some() && (time_due || count_due || stop) {
            do_ckpt(&mut st, &lat.links, &mut wall, &mut on_progress);
            last_ckpt = Instant::now();
            configs_since_ckpt = 0;
        }
        if stop && st.meas_sweeps_done < p.n_meas {
            st.elapsed += wall.elapsed().as_secs_f64();
            let g = finalize_glueball(p, &st);
            let s = finalize_sigma(p, &st);
            return (g, s, st.elapsed, false);
        }
    }

    st.elapsed += wall.elapsed().as_secs_f64();
    // Final checkpoint so a resume sees the completed chain (and not re-run).
    if let Some(path) = ckpt_path {
        st.links.clear();
        st.links.extend_from_slice(&lat.links);
        let _ = save_checkpoint(path, sig, &st);
    }
    let g = finalize_glueball(p, &st);
    let s = finalize_sigma(p, &st);
    (g, s, st.elapsed, true)
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

    #[test]
    fn neighbor_table_matches_lattice_shift() {
        // The O(1) neighbour table must agree with the coord()-arithmetic shift
        // for every (site, mu, direction) -- this is what keeps results
        // bit-identical to the pre-refactor engine.
        let lat = Lattice::new_hot(6, 3);
        let nb = Neighbors::new(&lat.geom());
        for site in 0..lat.vol {
            for mu in 0..DIM {
                assert_eq!(nb.fwd(site, mu), lat.shift(site, mu, true));
                assert_eq!(nb.bwd(site, mu), lat.shift(site, mu, false));
            }
        }
    }

    fn small_combined_params(seed: u64, threads: usize) -> CombinedParams {
        CombinedParams {
            l: 6,
            beta: 2.4,
            n_therm: 80,
            n_meas: 400,
            meas_interval: 4,
            n_overrelax: 2,
            smear_levels: vec![0, 2, 4],
            smear_alpha: 0.5,
            r_max: 2,
            t_max: 2,
            sigma_smear: 2,
            n_bins: 4,
            seed,
            threads,
        }
    }

    fn max_abs_diff(a: &[Vec<Vec<f64>>], b: &[Vec<Vec<f64>>]) -> f64 {
        let mut m = 0.0f64;
        for (ai, bi) in a.iter().zip(b) {
            for (aj, bj) in ai.iter().zip(bi) {
                for (x, y) in aj.iter().zip(bj) {
                    m = m.max((x - y).abs());
                }
            }
        }
        m
    }

    #[test]
    fn combined_chain_matches_separate_binaries() {
        // The merged single-chain measurement must reproduce, on the SAME seed,
        // exactly what the two separate binaries produce on their own chains
        // (same RNG stream -> same gauge configs -> same observables).  This is
        // the correctness guarantee for folding glueball + sigma onto one chain.
        let p = small_combined_params(7, 4);
        let (g, s, _e, finished) =
            measure_combined(&p, None, 0, 0.0, 0, |_, _, _| {});
        assert!(finished);

        let g_ref = measure_glueball(
            p.l, p.beta, p.n_therm, p.n_meas, p.meas_interval, p.n_overrelax,
            &p.smear_levels, p.smear_alpha, p.n_bins, p.seed, p.threads,
        );
        let s_ref = measure_string_tension(
            p.l, p.beta, p.n_therm, p.n_meas, p.meas_interval, p.n_overrelax,
            p.r_max, p.t_max, p.sigma_smear, p.smear_alpha, p.n_bins, p.seed, p.threads,
        );

        assert_eq!(g.n_collected, g_ref.n_collected);
        assert_eq!(s.n_collected, s_ref.n_collected);
        assert!(
            max_abs_diff(&g.corr, &g_ref.corr) < 1e-12,
            "0++ correlator differs from the standalone glueball binary"
        );
        assert!(
            max_abs_diff(&g.corr_E, &g_ref.corr_E) < 1e-12,
            "2++ E correlator differs from the standalone glueball binary"
        );
        let mut wmax = 0.0f64;
        for (rr, rr_ref) in s.w.iter().zip(&s_ref.w) {
            for (x, y) in rr.iter().zip(rr_ref) {
                wmax = wmax.max((x - y).abs());
            }
        }
        assert!(wmax < 1e-12, "Wilson-loop grid differs from the standalone string_tension binary (max {wmax:.2e})");
    }

    #[test]
    fn combined_is_thread_count_independent() {
        let (g1, s1, _, _) = measure_combined(&small_combined_params(11, 1), None, 0, 0.0, 0, |_, _, _| {});
        let (g4, s4, _, _) = measure_combined(&small_combined_params(11, 4), None, 0, 0.0, 0, |_, _, _| {});
        assert!(max_abs_diff(&g1.corr, &g4.corr) < 1e-12, "glueball corr depends on thread count");
        let mut wmax = 0.0f64;
        for (a, b) in s1.w.iter().zip(&s4.w) {
            for (x, y) in a.iter().zip(b) {
                wmax = wmax.max((x - y).abs());
            }
        }
        assert!(wmax < 1e-12, "sigma grid depends on thread count");
    }

    #[test]
    fn checkpoint_resume_matches_uninterrupted() {
        // A run interrupted after a checkpoint and resumed must reproduce the
        // uninterrupted run bit-for-bit (restored lattice + sweep_idx + bins).
        let p = small_combined_params(23, 2);
        let target = p.expected_configs();

        let (g_ref, s_ref, _, fin_ref) =
            measure_combined(&p, None, 0, 0.0, 0, |_, _, _| {});
        assert!(fin_ref);

        let mut ckpt = std::env::temp_dir();
        ckpt.push(format!("ym_ckpt_test_{}.bin", p.seed));
        let ckpt = ckpt.to_str().unwrap().to_string();
        let _ = std::fs::remove_file(&ckpt);

        // First leg: stop cleanly after ~40% of configs (writes the checkpoint).
        let (_pg, _ps, _e, fin1) =
            measure_combined(&p, Some(&ckpt), 0, 0.0, (target * 2) / 5, |_, _, _| {});
        assert!(!fin1, "first leg should have stopped early");

        // Second leg: resume from the checkpoint and finish.
        let (g2, s2, _e2, fin2) =
            measure_combined(&p, Some(&ckpt), 0, 0.0, 0, |_, _, _| {});
        assert!(fin2, "resumed leg should finish");
        assert_eq!(g2.n_collected, g_ref.n_collected, "resumed run collected a different config count");

        assert!(
            max_abs_diff(&g2.corr, &g_ref.corr) < 1e-12,
            "resumed 0++ correlator != uninterrupted"
        );
        assert!(
            max_abs_diff(&g2.corr_E, &g_ref.corr_E) < 1e-12,
            "resumed 2++ correlator != uninterrupted"
        );
        let mut wmax = 0.0f64;
        for (a, b) in s2.w.iter().zip(&s_ref.w) {
            for (x, y) in a.iter().zip(b) {
                wmax = wmax.max((x - y).abs());
            }
        }
        assert!(wmax < 1e-12, "resumed sigma grid != uninterrupted (max {wmax:.2e})");
        let _ = std::fs::remove_file(&ckpt);
    }
}
