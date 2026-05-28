//! 0++ glueball correlation-matrix measurement.  Runs the heatbath+overrelax
//! MCMC, builds smeared zero-momentum spatial-plaquette operators, and emits
//! the connected correlation matrix C_ij(tau) as JSON.  The Python side
//! (computations/long_runs/glueball_analysis.py) does the GEVP / effective-mass
//! plateau fit to extract the glueball mass in lattice units.
//!
//! Usage:
//!   glueball --L 16 --beta 2.4 --therm 2000 --meas 20000 --interval 4 \
//!       --overrelax 6 --smear-levels 0,4,8,16 --smear-alpha 0.5 --out g.json

use std::time::Instant;

use ym_simulations::measure_glueball;

fn main() {
    // defaults: a quick smoke configuration.
    let mut l = 8usize;
    let mut beta = 2.4f64;
    let mut therm = 500usize;
    let mut meas = 4000usize;
    let mut interval = 4usize;
    let mut overrelax = 4usize;
    let mut smear_levels = vec![0usize, 4, 8, 16];
    let mut smear_alpha = 0.5f64;
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
            "--smear-levels" => {
                smear_levels = val().split(',').map(|s| s.trim().parse().unwrap()).collect()
            }
            "--smear-alpha" => smear_alpha = val().parse().unwrap(),
            "--seed" => seed = val().parse().unwrap(),
            "--threads" => threads = val().parse().unwrap(),
            "--out" => out = Some(val()),
            other => panic!("unknown flag: {other}"),
        }
    }
    smear_levels.sort_unstable();
    smear_levels.dedup();

    eprintln!(
        "=== 0++ glueball (L={l}, beta={beta}, smear {smear_levels:?} @ alpha={smear_alpha}) ===\n  {therm} therm + {meas} meas (every {interval}), {overrelax} overrelax, {threads} threads"
    );
    let t0 = Instant::now();
    let g = measure_glueball(
        l, beta, therm, meas, interval, overrelax, &smear_levels, smear_alpha, seed, threads,
    );
    let secs = t0.elapsed().as_secs_f64();
    eprintln!("  collected {} configs in {:.1}s", g.n_collected, secs);

    // Sanity: effective mass of the most-smeared diagonal correlator.
    let top = g.smear_levels.len() - 1;
    eprintln!("  diag C_[{}][{}](tau) effective mass m_eff(tau)=ln(C(tau)/C(tau+1)):", top, top);
    let c = &g.corr[top][top];
    for tau in 0..c.len().saturating_sub(1) {
        let meff = if c[tau] > 0.0 && c[tau + 1] > 0.0 {
            (c[tau] / c[tau + 1]).ln()
        } else {
            f64::NAN
        };
        eprintln!("    tau={:>2}  C={:>14.6e}  m_eff={:.4}", tau, c[tau], meff);
    }

    // JSON.
    let fmt_vec = |v: &[f64]| -> String {
        v.iter().map(|x| format!("{x}")).collect::<Vec<_>>().join(", ")
    };
    let mut corr_json = String::new();
    corr_json.push('[');
    for (i, row) in g.corr.iter().enumerate() {
        if i > 0 {
            corr_json.push_str(", ");
        }
        corr_json.push('[');
        for (j, series) in row.iter().enumerate() {
            if j > 0 {
                corr_json.push_str(", ");
            }
            corr_json.push_str(&format!("[{}]", fmt_vec(series)));
        }
        corr_json.push(']');
    }
    corr_json.push(']');

    let levels_json = g
        .smear_levels
        .iter()
        .map(|x| x.to_string())
        .collect::<Vec<_>>()
        .join(", ");

    let json = format!(
        "{{\n  \"l\": {}, \"beta\": {}, \"n_therm\": {}, \"n_collected\": {},\n  \"smear_levels\": [{}], \"smear_alpha\": {}, \"n_overrelax\": {}, \"threads\": {},\n  \"meas_interval\": {}, \"elapsed_seconds\": {:.3},\n  \"mean_op\": [{}],\n  \"corr\": {}\n}}\n",
        g.l, g.beta, g.n_therm, g.n_collected,
        levels_json, g.smear_alpha, g.overrelax, g.threads,
        interval, secs,
        fmt_vec(&g.mean_op),
        corr_json
    );
    match &out {
        Some(p) => {
            std::fs::write(p, &json).expect("write json");
            eprintln!("\nJSON: {p}");
        }
        None => print!("{json}"),
    }
}
