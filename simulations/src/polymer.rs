//! Direct enumeration of connected lattice animals (polymers) via Redelmeier's
//! algorithm, for validating the Kotecky-Preiss connectivity assumption.
//!
//! The cluster-expansion bound (small-field-kp.tex) rests on the polymer count
//! N(n) <= e^{mu_conn n} with mu_conn = log(2d e) = log(8e) ~ 3.0794 at d=4 --
//! i.e. the growth constant of connected plaquette-polymers is bounded by
//! 8e ~ 21.75.  This module enumerates connected animals on (i) the 2D square
//! lattice -- validated against the fixed-polyomino sequence A001168
//! (1, 2, 6, 19, 63, 216, 760, 2725, ...) -- and (ii) the 4D plaquette graph
//! (share-a-link adjacency), measuring the actual growth constant to check the
//! bound and its tightness.
//!
//! Counting convention: fixed polyominoes (translation classes), via the
//! lex-minimal-cell Redelmeier discipline.  "Through a fixed plaquette" (rooted)
//! counts are R(n) = (subexponential) x N(n) with the same growth constant, so
//! the exponential rate -- all that mu_conn bounds -- is convention-independent.

/// A cell geometry: a contiguous, lex-ordered index space with a distinguished
/// origin (the lex-minimum) and a child function (neighbors with index > origin,
/// in board).
pub trait Geometry {
    fn board_size(&self) -> usize;
    fn origin(&self) -> usize;
    /// Append the in-board neighbors of `cell` with index > origin to `out`.
    fn children(&self, cell: usize, out: &mut Vec<usize>);
}

/// Redelmeier enumeration: returns counts[n] = number of fixed animals of size
/// n (n = 1..=max) whose lex-minimal cell is the origin.
pub fn count_animals<G: Geometry>(geom: &G, max: usize) -> Vec<u64> {
    let mut counts = vec![0u64; max + 1];
    let mut status = vec![false; geom.board_size()]; // true = blocked (in poly / candidate)
    let origin = geom.origin();
    status[origin] = true;
    counts[1] = 1;
    if max >= 2 {
        let mut untried = Vec::new();
        geom.children(origin, &mut untried);
        for &c in &untried {
            status[c] = true;
        }
        grow(geom, &mut status, &mut counts, untried, 1, max);
    }
    counts
}

fn grow<G: Geometry>(
    geom: &G,
    status: &mut [bool],
    counts: &mut [u64],
    untried: Vec<usize>,
    size: usize,
    max: usize,
) {
    if size == max {
        return;
    }
    let mut untried = untried;
    let mut child_buf: Vec<usize> = Vec::new();
    // Process candidates one at a time.  Popping c includes it (INCLUDE branch);
    // c then stays blocked for the rest of this loop (EXCLUDE branch).  c is
    // unblocked by the ancestor frame that first added it (via that frame's
    // `added` cleanup) -- never here -- which is the fix for the over-count.
    while let Some(c) = untried.pop() {
        counts[size + 1] += 1;
        child_buf.clear();
        geom.children(c, &mut child_buf);
        let mut added: Vec<usize> = Vec::new();
        for &nb in &child_buf {
            if !status[nb] {
                status[nb] = true;
                added.push(nb);
            }
        }
        if size + 1 < max {
            let mut sub = untried.clone();
            sub.extend_from_slice(&added);
            grow(geom, status, counts, sub, size + 1, max);
        }
        for &nb in &added {
            status[nb] = false;
        }
    }
}

// ---------------------------------------------------------------------------
// Parallel enumeration: decompose the Redelmeier tree into independent tasks
// at a fixed split depth, then run them across threads with a work queue.
// ---------------------------------------------------------------------------

use std::sync::atomic::{AtomicUsize, Ordering};

/// A resumable Redelmeier subtree: a partial polyomino at depth `size` with the
/// candidate `frontier` to extend and a set of `blocked` cells (poly + frontier
/// + forbidden) to seed the status array.  Counts sizes `size+1..=max`.
struct Task {
    blocked: Vec<usize>,
    frontier: Vec<usize>,
    size: usize,
}

/// Generate the depth-`split` tasks (serial; cheap), and the low-order counts
/// for sizes `1..=split` discovered along the way.  Mirrors `grow`'s discipline
/// but carries (poly, frontier, forbidden) explicitly so each node's state can
/// be snapshotted into an independent task.
fn gen_tasks<G: Geometry>(
    geom: &G,
    split: usize,
    poly: &[usize],
    frontier: &[usize],
    forbidden: &[usize],
    counts_low: &mut [u64],
    tasks: &mut Vec<Task>,
) {
    let size = poly.len();
    if size == split {
        let mut blocked = Vec::with_capacity(poly.len() + frontier.len() + forbidden.len());
        blocked.extend_from_slice(poly);
        blocked.extend_from_slice(frontier);
        blocked.extend_from_slice(forbidden);
        tasks.push(Task { blocked, frontier: frontier.to_vec(), size });
        return;
    }
    let mut frontier = frontier.to_vec();
    let mut forbidden = forbidden.to_vec();
    let mut child_buf: Vec<usize> = Vec::new();
    while let Some(c) = frontier.pop() {
        counts_low[size + 1] += 1;
        // c's new candidates: children not already in poly/frontier/forbidden.
        child_buf.clear();
        geom.children(c, &mut child_buf);
        let mut new_frontier = frontier.clone();
        for &nb in &child_buf {
            if !poly.contains(&nb)
                && !new_frontier.contains(&nb)
                && !forbidden.contains(&nb)
            {
                new_frontier.push(nb);
            }
        }
        let mut new_poly = poly.to_vec();
        new_poly.push(c);
        gen_tasks(geom, split, &new_poly, &new_frontier, &forbidden, counts_low, tasks);
        forbidden.push(c); // EXCLUDE c for subsequent siblings
    }
}

/// Parallel connected-animal count: identical result to `count_animals`, run
/// across `threads` via a work queue over depth-`split` subtrees.
pub fn count_animals_parallel<G: Geometry + Sync>(
    geom: &G,
    max: usize,
    threads: usize,
) -> Vec<u64> {
    if max < 4 || threads <= 1 {
        return count_animals(geom, max);
    }
    let split = 3.min(max - 1);

    // Generate tasks + low-order counts (serial, cheap).
    let mut counts_low = vec![0u64; max + 1];
    counts_low[1] = 1;
    let origin = geom.origin();
    let mut children0: Vec<usize> = Vec::new();
    geom.children(origin, &mut children0);
    let mut tasks: Vec<Task> = Vec::new();
    gen_tasks(geom, split, &[origin], &children0, &[], &mut counts_low, &mut tasks);

    // Work queue across threads.
    let cursor = AtomicUsize::new(0);
    let board = geom.board_size();
    let nthreads = threads.max(1).min(tasks.len().max(1));
    let partials: Vec<Vec<u64>> = std::thread::scope(|s| {
        let handles: Vec<_> = (0..nthreads)
            .map(|_| {
                let cursor = &cursor;
                let tasks = &tasks;
                s.spawn(move || {
                    let mut local = vec![0u64; max + 1];
                    let mut status = vec![false; board];
                    loop {
                        let i = cursor.fetch_add(1, Ordering::Relaxed);
                        if i >= tasks.len() {
                            break;
                        }
                        let t = &tasks[i];
                        for &c in &t.blocked {
                            status[c] = true;
                        }
                        grow(geom, &mut status, &mut local, t.frontier.clone(), t.size, max);
                        for &c in &t.blocked {
                            status[c] = false; // reset scratch for the next task
                        }
                    }
                    local
                })
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });

    let mut counts = counts_low;
    for p in partials {
        for n in 0..=max {
            counts[n] += p[n];
        }
    }
    counts
}

// ---------------------------------------------------------------------------
// 2D square lattice (validation against A001168).
// ---------------------------------------------------------------------------

pub struct Square2D {
    pub n: i64, // board half-width
    bx: i64,    // x in [0, n]  (origin is x-minimum)
    by: i64,    // y in [-n, n]
    origin_idx: usize,
}

impl Square2D {
    pub fn new(n: usize) -> Self {
        let n = n as i64;
        let bx = n + 1;
        let by = 2 * n + 1;
        // origin = (x=0, y=0); idx = x*by + (y+n)
        let origin_idx = (0 * by + (0 + n)) as usize;
        Square2D { n, bx, by, origin_idx }
    }
    #[inline]
    fn pack(&self, x: i64, y: i64) -> Option<usize> {
        if x < 0 || x > self.n || y < -self.n || y > self.n {
            return None;
        }
        Some((x * self.by + (y + self.n)) as usize)
    }
    #[inline]
    fn unpack(&self, idx: usize) -> (i64, i64) {
        let idx = idx as i64;
        let x = idx / self.by;
        let y = idx % self.by - self.n;
        (x, y)
    }
}

impl Geometry for Square2D {
    fn board_size(&self) -> usize {
        (self.bx * self.by) as usize
    }
    fn origin(&self) -> usize {
        self.origin_idx
    }
    fn children(&self, cell: usize, out: &mut Vec<usize>) {
        let (x, y) = self.unpack(cell);
        for (dx, dy) in [(1, 0), (-1, 0), (0, 1), (0, -1)] {
            if let Some(idx) = self.pack(x + dx, y + dy) {
                if idx > self.origin_idx {
                    out.push(idx);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// 4D plaquette graph (share-a-link adjacency).
// ---------------------------------------------------------------------------

/// The 6 oriented planes (mu < nu) in 4D, indexed 0..6.
const PLANES: [(usize, usize); 6] = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)];

#[inline]
fn plane_of(mu: usize, nu: usize) -> usize {
    let (a, b) = if mu < nu { (mu, nu) } else { (nu, mu) };
    PLANES.iter().position(|&p| p == (a, b)).unwrap()
}

pub struct Plaq4D {
    pub n: i64, // board half-width
    s1: i64,    // 2n+1
    origin_idx: usize,
}

impl Plaq4D {
    pub fn new(n: usize) -> Self {
        let n = n as i64;
        let s1 = 2 * n + 1;
        // x0 in [0, n], x1,x2,x3 in [-n, n], o in 0..6.
        // idx = ((((x0)*s1 + (x1+n))*s1 + (x2+n))*s1 + (x3+n))*6 + o
        let origin_idx = ((((0 * s1 + n) * s1 + n) * s1 + n) * 6) as usize;
        Plaq4D { n, s1, origin_idx }
    }
    #[inline]
    fn pack(&self, x: [i64; 4], o: usize) -> Option<usize> {
        if x[0] < 0 || x[0] > self.n {
            return None;
        }
        for k in 1..4 {
            if x[k] < -self.n || x[k] > self.n {
                return None;
            }
        }
        let s1 = self.s1;
        let idx = ((((x[0]) * s1 + (x[1] + self.n)) * s1 + (x[2] + self.n)) * s1
            + (x[3] + self.n))
            * 6
            + o as i64;
        Some(idx as usize)
    }
    #[inline]
    fn unpack(&self, idx: usize) -> ([i64; 4], usize) {
        let mut r = idx as i64;
        let o = (r % 6) as usize;
        r /= 6;
        let x3 = r % self.s1 - self.n;
        r /= self.s1;
        let x2 = r % self.s1 - self.n;
        r /= self.s1;
        let x1 = r % self.s1 - self.n;
        r /= self.s1;
        let x0 = r;
        ([x0, x1, x2, x3], o)
    }

    /// Plaquettes sharing the link (site `y`, direction `lambda`), appended to `out`.
    fn plaqs_of_link(&self, y: [i64; 4], lambda: usize, out: &mut Vec<usize>) {
        for sigma in 0..4 {
            if sigma == lambda {
                continue;
            }
            let o = plane_of(lambda, sigma);
            // base y (link is the lambda-edge at the base corner)
            if let Some(i) = self.pack(y, o) {
                out.push(i);
            }
            // base y - e_sigma (link is the shifted lambda-edge)
            let mut yb = y;
            yb[sigma] -= 1;
            if let Some(i) = self.pack(yb, o) {
                out.push(i);
            }
        }
    }
}

impl Geometry for Plaq4D {
    fn board_size(&self) -> usize {
        ((self.n + 1) * self.s1 * self.s1 * self.s1 * 6) as usize
    }
    fn origin(&self) -> usize {
        self.origin_idx
    }
    fn children(&self, cell: usize, out: &mut Vec<usize>) {
        let (x, o) = self.unpack(cell);
        let (mu, nu) = PLANES[o];
        // 4 links of plaquette (x, mu, nu): (x,mu),(x+nu,mu),(x,nu),(x+mu,nu)
        let mut x_pnu = x;
        x_pnu[nu] += 1;
        let mut x_pmu = x;
        x_pmu[mu] += 1;
        let links = [(x, mu), (x_pnu, mu), (x, nu), (x_pmu, nu)];
        let mut tmp: Vec<usize> = Vec::with_capacity(24);
        for (y, lam) in links {
            self.plaqs_of_link(y, lam, &mut tmp);
        }
        tmp.sort_unstable();
        tmp.dedup();
        for idx in tmp {
            if idx != cell && idx > self.origin_idx {
                out.push(idx);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn square2d_matches_a001168() {
        // Fixed polyominoes: 1, 2, 6, 19, 63, 216, 760, 2725, ...
        let expected = [0u64, 1, 2, 6, 19, 63, 216, 760];
        let geom = Square2D::new(expected.len());
        let counts = count_animals(&geom, expected.len() - 1);
        for n in 1..expected.len() {
            assert_eq!(counts[n], expected[n], "A001168 mismatch at n={n}");
        }
    }

    #[test]
    fn plaq4d_full_neighbor_count_is_20() {
        // An interior plaquette shares a link with exactly 20 others.
        let geom = Plaq4D::new(4);
        // count ALL neighbors (not just children) of a deep-interior plaquette
        // by using plaqs_of_link directly.
        let x = [2i64, 0, 0, 0];
        let o = 0usize; // plane (0,1)
        let (mu, nu) = PLANES[o];
        let mut x_pnu = x;
        x_pnu[nu] += 1;
        let mut x_pmu = x;
        x_pmu[mu] += 1;
        let links = [(x, mu), (x_pnu, mu), (x, nu), (x_pmu, nu)];
        let mut tmp = Vec::new();
        for (y, lam) in links {
            geom.plaqs_of_link(y, lam, &mut tmp);
        }
        let self_idx = geom.pack(x, o).unwrap();
        tmp.sort_unstable();
        tmp.dedup();
        let n_neighbors = tmp.iter().filter(|&&i| i != self_idx).count();
        assert_eq!(n_neighbors, 20, "plaquette should have 20 link-neighbors");
    }

    #[test]
    fn plaq4d_small_counts_positive_and_growing() {
        let geom = Plaq4D::new(6);
        let counts = count_animals(&geom, 5);
        assert_eq!(counts[1], 1);
        for n in 2..=5 {
            assert!(counts[n] > counts[n - 1], "counts should grow: {:?}", counts);
        }
    }

    #[test]
    fn parallel_matches_serial_plaq4d() {
        let geom = Plaq4D::new(6);
        let serial = count_animals(&geom, 6);
        for threads in [2usize, 4, 8, 16] {
            let par = count_animals_parallel(&geom, 6, threads);
            assert_eq!(serial, par, "parallel != serial at {threads} threads");
        }
    }

    #[test]
    fn parallel_matches_serial_square2d() {
        let geom = Square2D::new(8);
        let serial = count_animals(&geom, 8);
        let par = count_animals_parallel(&geom, 8, 8);
        assert_eq!(serial, par);
    }
}
