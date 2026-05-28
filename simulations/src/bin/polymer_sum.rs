//! Direct polymer enumeration on the 4D plaquette graph: count connected
//! plaquette-animals N(n) up to size `max`, measure the growth constant, and
//! check it against the cluster-expansion bound mu_conn = log(2d e) = log(8e),
//! plus the KP partition sums and the conjecture-7.4 union-bound looseness at
//! the polymer level.
//!
//! Validates the load-bearing connectivity assumption of small-field-kp.tex:
//! the polymer count must satisfy N(n) <= e^{mu_conn n}, i.e. the growth
//! constant lambda = lim N(n)^{1/n} <= 8e ~ 21.75 (mu_emp = ln lambda <= 3.079).
//!
//! Usage:
//!   polymer_sum --max 7 --rho-sf 8.33 --rho-lf 5.0 --out p.json
//! (rho_sf = c_lambda * kappa / g^2; canonical g_0=0.30 => rho_sf = 0.75/0.09 = 8.33.)

use std::time::Instant;

use ym_simulations::polymer::{count_animals_parallel, Plaq4D};

const MU_CONN: f64 = 3.0794415416798357; // log(8e), d=4

fn kp_sum(counts: &[u64], rho: f64) -> f64 {
    // S(rho) = sum_{n>=1} N(n) e^{-rho n}  (truncated at the enumerated max)
    counts
        .iter()
        .enumerate()
        .skip(1)
        .map(|(n, &cn)| cn as f64 * (-rho * n as f64).exp())
        .sum()
}

fn main() {
    let mut max = 6usize;
    let mut rho_sf = 8.333f64; // canonical g_0=0.30: c_lambda*kappa/g^2 = 0.75/0.09
    let mut rho_lf = 5.0f64;
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
            "--max" => max = val().parse().unwrap(),
            "--rho-sf" => rho_sf = val().parse().unwrap(),
            "--rho-lf" => rho_lf = val().parse().unwrap(),
            "--threads" => threads = val().parse().unwrap(),
            "--out" => out = Some(val()),
            other => panic!("unknown flag: {other}"),
        }
    }

    eprintln!("=== 4D plaquette polymer enumeration (max size = {max}, {threads} threads) ===");
    let t0 = Instant::now();
    let geom = Plaq4D::new(max);
    let counts = count_animals_parallel(&geom, max, threads);
    let secs = t0.elapsed().as_secs_f64();

    eprintln!("  N(n) = connected plaquette-animals (lex-min = fixed origin):");
    let mut mu_max: f64 = 0.0;
    for n in 1..=max {
        let ratio = if n >= 2 && counts[n - 1] > 0 {
            counts[n] as f64 / counts[n - 1] as f64
        } else {
            f64::NAN
        };
        let mu_emp = if ratio.is_finite() { ratio.ln() } else { f64::NAN };
        if mu_emp.is_finite() {
            mu_max = mu_max.max(mu_emp);
        }
        eprintln!(
            "    N({n:>2}) = {:>16}   N(n)/N(n-1) = {:>8.4}   mu_emp = {:.4}",
            counts[n], ratio, mu_emp
        );
    }
    eprintln!(
        "  growth: max mu_emp (n>=2) = {:.4}   vs  mu_conn = log(8e) = {:.4}   => bound {}",
        mu_max,
        MU_CONN,
        if mu_max <= MU_CONN { "HOLDS" } else { "VIOLATED" }
    );
    eprintln!("    (enumeration took {secs:.1}s)");

    // KP partition sums vs the closed-form geometric bound.
    eprintln!("  KP sums S(rho) = sum N(n) e^{{-rho n}}  vs  closed form 1/(1-e^{{-(rho-mu_conn)}}):");
    let s_sf = kp_sum(&counts, rho_sf);
    let s_lf = kp_sum(&counts, rho_lf);
    for (name, rho, s) in [("sf", rho_sf, s_sf), ("lf", rho_lf, s_lf)] {
        let kclosed = if rho > MU_CONN {
            1.0 / (1.0 - (-(rho - MU_CONN)).exp())
        } else {
            f64::INFINITY
        };
        eprintln!(
            "    rho_{name} = {rho:.3}:  S_exact = {s:.6e}   K_closed = {kclosed:.6}   S<=K: {}",
            s <= kclosed
        );
    }

    // Conjecture 7.4 union bound at the polymer level: with size-only
    // activities, max(e^{-rho_sf n}, e^{-rho_lf n}) = e^{-min n}, so
    // K_cap = S(min(rho_sf,rho_lf)); looseness = (S_sf + S_lf)/K_cap.
    let rho_min = rho_sf.min(rho_lf);
    let s_cap = kp_sum(&counts, rho_min);
    let looseness = (s_sf + s_lf) / s_cap;
    eprintln!(
        "  conjecture 7.4 (polymer level): K_cap = S(min) = {s_cap:.6e};  union looseness (S_sf+S_lf)/K_cap = {looseness:.4}"
    );
    eprintln!("    (K-level empirical reference: 1.014 at g_0=0.30, <= 1.176 across the regime)");

    // JSON.
    let counts_json = counts[1..=max]
        .iter()
        .map(|c| c.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    let json = format!(
        "{{\n  \"max\": {}, \"mu_conn\": {}, \"mu_emp_max\": {},\n  \"rho_sf\": {}, \"rho_lf\": {},\n  \"S_sf\": {}, \"S_lf\": {}, \"S_cap_min\": {}, \"union_looseness\": {},\n  \"elapsed_seconds\": {:.3},\n  \"counts\": [{}]\n}}\n",
        max, MU_CONN, mu_max, rho_sf, rho_lf, s_sf, s_lf, s_cap, looseness, secs, counts_json
    );
    match &out {
        Some(p) => {
            std::fs::write(p, &json).expect("write json");
            eprintln!("\nJSON: {p}");
        }
        None => print!("{json}"),
    }
}
