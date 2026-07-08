//! Block-spin defect measurement for SU(2): correlated fine-vs-blocked Wilson
//! loops + plaquette, for a family of factor-2 real-space blocking schemes with
//! a tunable transverse bond-move weight `lambda`.
//!
//! For each collected config we measure, on the SAME configuration:
//!   * the fine average plaquette and the fine Wilson-loop grid W(r,t),
//!   * for each blocking scheme (lambda), the blocked config on the (L/2)^4
//!     lattice, its average plaquette, and its Wilson-loop grid W'(r,t).
//! Everything is accumulated into contiguous configuration bins so the Python
//! side can form CORRELATED jackknife ratios (blocked vs fine, same configs),
//! which is what makes the per-step defect ratio delta_k precise.
//!
//! Blocking (factor 2, isotropic, 4D).  The blocked link from block-site X to
//! X+mu (fine sites 2X -> 2X+2mu) is
//!   V_mu(X) = renorm( S_straight + lambda * sum_{nu != mu} (D_nu^+ + D_nu^-) )
//! where S_straight = U_mu(2X) U_mu(2X+mu) is the on-axis product and D_nu^+/-
//! are the two transverse detours (go +/-nu, two mu-steps, come back).  All
//! paths share the endpoints 2X, 2X+2mu, so V transforms covariantly under
//! gauge transformations at the surviving (block-centre) sites.  lambda=0 is
//! pure decimation; lambda>0 is Migdal-Kadanoff-style transverse bond-moving.
//!
//! Usage:
//!   block_defect --L 16 --beta 2.4 --therm 2000 --meas 20000 --interval 4 \
//!       --overrelax 4 --rmax 6 --lambdas 0.0,0.5,1.0 --bins 40 --seed 7 \
//!       --out out.json

use std::time::Instant;

use ym_simulations::{build_classes, dag, mul, renorm, sweep, Geom, Lattice, Neighbors, Su2, DIM, ID};

#[inline]
fn get(links: &[Su2], site: usize, mu: usize) -> Su2 {
    links[site * DIM + mu]
}

/// Blocked geometry for side length `m = L/2`.
fn blocked_geom(m: usize) -> Geom {
    Geom { l: m, vol: m.pow(DIM as u32), strides: [m * m * m, m * m, m, 1] }
}

/// Fine site index of the block-centre 2*X, where X is a blocked-lattice site.
fn fine_center(bg: &Geom, fg: &Geom, xblk: usize) -> usize {
    let mut f = 0usize;
    for d in 0..DIM {
        let xd = (xblk / bg.strides[d]) % bg.l;
        f += (2 * xd) * fg.strides[d];
    }
    f
}

/// Build the blocked link buffer for a given transverse weight `lambda`.
fn block_links(fine: &[Su2], nbf: &Neighbors, fg: &Geom, bg: &Geom, lambda: f64) -> Vec<Su2> {
    let mut out = vec![ID; bg.vol * DIM];
    for xblk in 0..bg.vol {
        let f0 = fine_center(bg, fg, xblk);
        for mu in 0..DIM {
            // On-axis straight product U_mu(f0) U_mu(f0+mu).
            let f0_pmu = nbf.fwd(f0, mu);
            let mut acc = mul(get(fine, f0, mu), get(fine, f0_pmu, mu));
            if lambda != 0.0 {
                let f0_2mu = nbf.fwd(f0_pmu, mu); // 2X + 2mu
                for nu in 0..DIM {
                    if nu == mu {
                        continue;
                    }
                    // Upper detour: +nu, +mu, +mu, then -nu.
                    let a1 = nbf.fwd(f0, nu); // 2X+nu
                    let a2 = nbf.fwd(a1, mu); // 2X+nu+mu
                    let dplus = mul(
                        mul(mul(get(fine, f0, nu), get(fine, a1, mu)), get(fine, a2, mu)),
                        dag(get(fine, f0_2mu, nu)),
                    );
                    // Lower detour: -nu, +mu, +mu, then +nu.
                    let bm = nbf.bwd(f0, nu); // 2X-nu
                    let bm1 = nbf.fwd(bm, mu); // 2X-nu+mu
                    let bm2 = nbf.fwd(bm1, mu); // 2X-nu+2mu
                    let dminus = mul(
                        mul(mul(dag(get(fine, bm, nu)), get(fine, bm, mu)), get(fine, bm1, mu)),
                        get(fine, bm2, nu),
                    );
                    acc = [
                        acc[0] + lambda * (dplus[0] + dminus[0]),
                        acc[1] + lambda * (dplus[1] + dminus[1]),
                        acc[2] + lambda * (dplus[2] + dminus[2]),
                        acc[3] + lambda * (dplus[3] + dminus[3]),
                    ];
                }
            }
            out[xblk * DIM + mu] = renorm(acc);
        }
    }
    out
}

/// Average plaquette (1/2)Re Tr U_plaq over all plaquettes of a links buffer.
fn avg_plaq(links: &[Su2], nb: &Neighbors) -> f64 {
    let mut sum = 0.0f64;
    let mut count = 0u64;
    for site in 0..nb.vol {
        for mu in 0..DIM {
            for nu in (mu + 1)..DIM {
                let x_pmu = nb.fwd(site, mu);
                let x_pnu = nb.fwd(site, nu);
                let up = mul(
                    mul(get(links, site, mu), get(links, x_pmu, nu)),
                    mul(dag(get(links, x_pnu, mu)), dag(get(links, site, nu))),
                );
                sum += up[0];
                count += 1;
            }
        }
    }
    sum / count as f64
}

/// Planar Wilson-loop grid W(r,t), r,t in 1..=rmax (spatial r in dirs 1..3,
/// temporal t in dir 0), averaged over sites and the 3 spatial directions.
/// Returns a flat rmax*rmax grid, w[(r-1)*rmax + (t-1)].
fn wilson_grid(links: &[Su2], nb: &Neighbors, rmax: usize) -> Vec<f64> {
    let vol = nb.vol;
    // Temporal lines tl[t][x] = product of t temporal links from x.
    let mut tl = vec![vec![ID; vol]; rmax + 1];
    for x in 0..vol {
        tl[1][x] = get(links, x, 0);
    }
    for t in 2..=rmax {
        for x in 0..vol {
            let xp = nb.shift_n(x, 0, t - 1, true);
            tl[t][x] = mul(tl[t - 1][x], get(links, xp, 0));
        }
    }
    let mut w = vec![0.0f64; rmax * rmax];
    for i in 1..DIM {
        // Spatial lines sl[r][x] = product of r links in dir i from x.
        let mut sl = vec![vec![ID; vol]; rmax + 1];
        for x in 0..vol {
            sl[1][x] = get(links, x, i);
        }
        for r in 2..=rmax {
            for x in 0..vol {
                let xp = nb.shift_n(x, i, r - 1, true);
                sl[r][x] = mul(sl[r - 1][x], get(links, xp, i));
            }
        }
        for x in 0..vol {
            for r in 1..=rmax {
                let x_pr = nb.shift_n(x, i, r, true);
                for t in 1..=rmax {
                    let x_pt = nb.shift_n(x, 0, t, true);
                    let lp = mul(
                        mul(sl[r][x], tl[t][x_pr]),
                        mul(dag(sl[r][x_pt]), dag(tl[t][x])),
                    );
                    w[(r - 1) * rmax + (t - 1)] += lp[0];
                }
            }
        }
    }
    let norm = (vol * (DIM - 1)) as f64;
    for v in w.iter_mut() {
        *v /= norm;
    }
    w
}

fn parse_lambdas(s: &str) -> Vec<f64> {
    s.split(',').map(|x| x.trim().parse().unwrap()).collect()
}

fn fvec(v: &[f64]) -> String {
    v.iter().map(|x| format!("{x}")).collect::<Vec<_>>().join(", ")
}

fn main() {
    let mut l = 12usize;
    let mut beta = 2.4f64;
    let mut therm = 1000usize;
    let mut meas = 8000usize;
    let mut interval = 4usize;
    let mut overrelax = 4usize;
    let mut rmax = 6usize; // fine loop extent; blocked uses rmax/2
    let mut lambdas = vec![0.0f64, 0.5, 1.0];
    let mut bins = 40usize;
    let mut seed = 0u64;
    let mut threads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1);
    let mut out: Option<String> = None;

    let argv: Vec<String> = std::env::args().collect();
    let mut i = 1;
    while i < argv.len() {
        let key = argv[i].clone();
        i += 1;
        let mut val = || {
            let v = argv.get(i).cloned().unwrap_or_else(|| panic!("missing value for {key}"));
            i += 1;
            v
        };
        match key.as_str() {
            "--L" => l = val().parse().unwrap(),
            "--beta" => beta = val().parse().unwrap(),
            "--therm" => therm = val().parse().unwrap(),
            "--meas" => meas = val().parse().unwrap(),
            "--interval" => interval = val().parse().unwrap(),
            "--overrelax" => overrelax = val().parse().unwrap(),
            "--rmax" => rmax = val().parse().unwrap(),
            "--lambdas" => lambdas = parse_lambdas(&val()),
            "--bins" => bins = val().parse().unwrap(),
            "--seed" => seed = val().parse().unwrap(),
            "--threads" => threads = val().parse().unwrap(),
            "--out" => out = Some(val()),
            other => panic!("unknown flag: {other}"),
        }
    }
    assert!(l % 2 == 0, "L must be even for factor-2 blocking");
    let m = l / 2;
    let rmax_b = (rmax / 2).min(m - 1);
    assert!(rmax < l, "rmax must be < L");

    eprintln!(
        "=== block-spin defect (L={l}, beta={beta}, rmax={rmax}, rmax_blocked={rmax_b}, lambdas={lambdas:?}) ===\n  {therm} therm + {meas} meas (every {interval}), {overrelax} overrelax, {threads} threads, {bins} bins"
    );

    let t0 = Instant::now();
    let mut lat = Lattice::new_hot(l, seed);
    let classes = build_classes(&lat);
    let fg = lat.geom();
    let nbf = Neighbors::new(&fg);
    let bg = blocked_geom(m);
    let nbb = Neighbors::new(&bg);
    let nlam = lambdas.len();

    let mut sweep_idx: u64 = 0;
    for _ in 0..therm {
        sweep(&mut lat, beta, overrelax, sweep_idx, seed, threads, &classes, &nbf);
        sweep_idx += 1;
    }

    // Binning.
    let expected = (meas / interval.max(1)).max(1);
    let n_bins = bins.clamp(1, expected);
    let bin_size = (expected + n_bins - 1) / n_bins;

    let mut bin_counts = vec![0usize; n_bins];
    let mut fine_plaq = vec![0.0f64; n_bins];
    let mut fine_w = vec![vec![0.0f64; rmax * rmax]; n_bins];
    // blocked: per lambda.
    let mut blk_plaq = vec![vec![0.0f64; n_bins]; nlam];
    let mut blk_w = vec![vec![vec![0.0f64; rmax_b * rmax_b]; n_bins]; nlam];

    let mut n_collected = 0usize;
    let mut since = 0usize;
    for _ in 0..meas {
        sweep(&mut lat, beta, overrelax, sweep_idx, seed, threads, &classes, &nbf);
        sweep_idx += 1;
        since += 1;
        if since < interval {
            continue;
        }
        since = 0;
        let bin = (n_collected / bin_size).min(n_bins - 1);
        bin_counts[bin] += 1;

        // Fine observables.
        fine_plaq[bin] += avg_plaq(&lat.links, &nbf);
        let fw = wilson_grid(&lat.links, &nbf, rmax);
        for (k, v) in fw.iter().enumerate() {
            fine_w[bin][k] += *v;
        }

        // Blocked observables per scheme.
        for (li, &lam) in lambdas.iter().enumerate() {
            let vlinks = block_links(&lat.links, &nbf, &fg, &bg, lam);
            blk_plaq[li][bin] += avg_plaq(&vlinks, &nbb);
            let bw = wilson_grid(&vlinks, &nbb, rmax_b);
            for (k, v) in bw.iter().enumerate() {
                blk_w[li][bin][k] += *v;
            }
        }
        n_collected += 1;
    }
    let secs = t0.elapsed().as_secs_f64();
    eprintln!("  collected {n_collected} configs in {secs:.1}s");

    // Quick sanity to stderr: fine chi(2,2), blocked chi(2,2) for each lambda.
    let nc = n_collected.max(1) as f64;
    let creutz = |w: &[f64], rm: usize, r: usize| -> f64 {
        let g = |a: usize, b: usize| w[(a - 1) * rm + (b - 1)] / nc;
        let num = g(r, r) * g(r - 1, r - 1);
        let den = g(r, r - 1) * g(r - 1, r);
        if num > 0.0 && den > 0.0 { -(num / den).ln() } else { f64::NAN }
    };
    // Aggregate grids for the sanity print.
    let mut fw_tot = vec![0.0f64; rmax * rmax];
    for b in 0..n_bins {
        for k in 0..rmax * rmax {
            fw_tot[k] += fine_w[b][k];
        }
    }
    let fp: f64 = fine_plaq.iter().sum::<f64>() / nc;
    eprintln!("  fine  <P>={fp:.4}  chi(2,2)={:.4} chi(3,3)={:.4}", creutz(&fw_tot, rmax, 2), creutz(&fw_tot, rmax, 3.min(rmax)));
    for (li, &lam) in lambdas.iter().enumerate() {
        let mut bw_tot = vec![0.0f64; rmax_b * rmax_b];
        for b in 0..n_bins {
            for k in 0..rmax_b * rmax_b {
                bw_tot[k] += blk_w[li][b][k];
            }
        }
        let bp: f64 = blk_plaq[li].iter().sum::<f64>() / nc;
        let chi2 = if rmax_b >= 2 { creutz(&bw_tot, rmax_b, 2) } else { f64::NAN };
        eprintln!("  blk λ={lam:.2}  <P'>={bp:.4}  chi'(2,2)={chi2:.4}");
    }

    // JSON.
    let grid_bins = |g: &[Vec<f64>]| -> String {
        g.iter().map(|row| format!("[{}]", fvec(row))).collect::<Vec<_>>().join(", ")
    };
    let counts = bin_counts.iter().map(|c| c.to_string()).collect::<Vec<_>>().join(", ");
    let mut blocked_json = String::from("[");
    for (li, &lam) in lambdas.iter().enumerate() {
        if li > 0 {
            blocked_json.push_str(", ");
        }
        blocked_json.push_str(&format!(
            "{{\"lambda\": {}, \"rmax\": {}, \"bin_plaq_sum\": [{}], \"bin_w_sum\": [{}]}}",
            lam,
            rmax_b,
            fvec(&blk_plaq[li]),
            grid_bins(&blk_w[li]),
        ));
    }
    blocked_json.push(']');

    let json = format!(
        "{{\n  \"l\": {l}, \"beta\": {beta}, \"n_therm\": {therm}, \"n_collected\": {n_collected},\n  \"meas_interval\": {interval}, \"n_overrelax\": {overrelax}, \"threads\": {threads}, \"elapsed_seconds\": {secs:.3},\n  \"rmax\": {rmax}, \"rmax_blocked\": {rmax_b}, \"lambdas\": [{}],\n  \"n_bins\": {n_bins}, \"bin_counts\": [{counts}],\n  \"fine\": {{\"rmax\": {rmax}, \"bin_plaq_sum\": [{}], \"bin_w_sum\": [{}]}},\n  \"blocked\": {blocked_json}\n}}\n",
        fvec(&lambdas),
        fvec(&fine_plaq),
        grid_bins(&fine_w),
    );
    match &out {
        Some(p) => {
            std::fs::write(p, &json).expect("write json");
            eprintln!("JSON: {p}");
        }
        None => print!("{json}"),
    }
}
