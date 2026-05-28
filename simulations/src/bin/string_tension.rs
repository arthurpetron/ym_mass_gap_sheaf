//! String-tension measurement: rectangular Wilson loops W(R,T) -> JSON.
//! The Python side (computations/long_runs/string_tension_analysis.py)
//! extracts sigma via Creutz ratios and the static-potential fit.
//!
//! Usage:
//!   string_tension --L 16 --beta 2.4 --therm 3000 --meas 40000 --interval 5 \
//!       --overrelax 6 --rmax 8 --tmax 8 --smear 4 --smear-alpha 0.5 --out s.json

use std::time::Instant;

use ym_simulations::measure_string_tension;

fn main() {
    let mut l = 8usize;
    let mut beta = 2.4f64;
    let mut therm = 500usize;
    let mut meas = 4000usize;
    let mut interval = 5usize;
    let mut overrelax = 4usize;
    let mut rmax = 4usize;
    let mut tmax = 4usize;
    let mut smear = 0usize;
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
            "--rmax" => rmax = val().parse().unwrap(),
            "--tmax" => tmax = val().parse().unwrap(),
            "--smear" => smear = val().parse().unwrap(),
            "--smear-alpha" => smear_alpha = val().parse().unwrap(),
            "--seed" => seed = val().parse().unwrap(),
            "--threads" => threads = val().parse().unwrap(),
            "--out" => out = Some(val()),
            other => panic!("unknown flag: {other}"),
        }
    }

    eprintln!(
        "=== string tension (L={l}, beta={beta}, Rmax={rmax}, Tmax={tmax}, smear={smear}@{smear_alpha}) ===\n  {therm} therm + {meas} meas (every {interval}), {overrelax} overrelax, {threads} threads"
    );
    let t0 = Instant::now();
    let s = measure_string_tension(
        l, beta, therm, meas, interval, overrelax, rmax, tmax, smear, smear_alpha, seed, threads,
    );
    let secs = t0.elapsed().as_secs_f64();
    eprintln!("  collected {} configs in {:.1}s", s.n_collected, secs);

    // Sanity: diagonal Creutz ratios chi(r,r) -> sigma (lattice units).
    eprintln!("  Creutz ratios chi(r,r) = -ln[W(r,r)W(r-1,r-1)/(W(r-1,r)W(r,r-1))]:");
    for r in 2..=rmax {
        let w = |a: usize, b: usize| s.w[a - 1][b - 1];
        let num = w(r, r) * w(r - 1, r - 1);
        let den = w(r, r - 1) * w(r - 1, r);
        let chi = if num > 0.0 && den > 0.0 {
            -(num / den).ln()
        } else {
            f64::NAN
        };
        eprintln!("    chi({r},{r}) = {chi:.5}  (sqrt = {:.4})", chi.max(0.0).sqrt());
    }

    // JSON: emit the full W(R,T) grid.
    let mut rows = String::new();
    rows.push('[');
    for (ri, row) in s.w.iter().enumerate() {
        if ri > 0 {
            rows.push_str(", ");
        }
        let series = row.iter().map(|x| format!("{x}")).collect::<Vec<_>>().join(", ");
        rows.push_str(&format!("[{series}]"));
    }
    rows.push(']');

    let json = format!(
        "{{\n  \"l\": {}, \"beta\": {}, \"n_therm\": {}, \"n_collected\": {},\n  \"r_max\": {}, \"t_max\": {}, \"smear_steps\": {}, \"smear_alpha\": {}, \"n_overrelax\": {}, \"threads\": {},\n  \"meas_interval\": {}, \"elapsed_seconds\": {:.3},\n  \"w\": {}\n}}\n",
        s.l, s.beta, s.n_therm, s.n_collected,
        s.r_max, s.t_max, s.smear_steps, s.smear_alpha, s.overrelax, s.threads,
        interval, secs, rows
    );
    match &out {
        Some(p) => {
            std::fs::write(p, &json).expect("write json");
            eprintln!("\nJSON: {p}");
        }
        None => print!("{json}"),
    }
}
