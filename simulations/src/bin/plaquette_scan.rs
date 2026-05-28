//! Average-plaquette scan over a (beta, L) grid using the heatbath+overrelax
//! engine.  Emits JSON consumed by the Python plotting pipeline.
//!
//! Usage:
//!   plaquette_scan --betas 2.0,2.4,2.8 --L 8,12 --therm 1000 --meas 2000 \
//!       --interval 5 --overrelax 4 --seed 0 --out path.json
//!
//! Defaults reproduce a quick cross-check grid.  The JSON schema mirrors
//! computations/long_runs/mcmc_continuum_scan.py so the Python reader can
//! consume either source.

use std::time::Instant;

use ym_simulations::run_mcmc;

struct Args {
    betas: Vec<f64>,
    ells: Vec<usize>,
    therm: usize,
    meas: usize,
    interval: usize,
    overrelax: usize,
    seed: u64,
    threads: usize,
    out: Option<String>,
}

fn parse_args() -> Args {
    let mut a = Args {
        betas: vec![1.5, 2.0, 2.4, 2.8, 3.2, 4.0],
        ells: vec![4],
        therm: 500,
        meas: 1000,
        interval: 5,
        overrelax: 4,
        seed: 0,
        threads: std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1),
        out: None,
    };
    let argv: Vec<String> = std::env::args().collect();
    let mut i = 1;
    while i < argv.len() {
        let key = argv[i].as_str();
        let mut next = || {
            i += 1;
            argv.get(i).cloned().unwrap_or_else(|| panic!("missing value for {key}"))
        };
        match key {
            "--betas" => {
                a.betas = next().split(',').map(|s| s.trim().parse().unwrap()).collect();
            }
            "--L" => {
                a.ells = next().split(',').map(|s| s.trim().parse().unwrap()).collect();
            }
            "--therm" => a.therm = next().parse().unwrap(),
            "--meas" => a.meas = next().parse().unwrap(),
            "--interval" => a.interval = next().parse().unwrap(),
            "--overrelax" => a.overrelax = next().parse().unwrap(),
            "--seed" => a.seed = next().parse().unwrap(),
            "--threads" => a.threads = next().parse().unwrap(),
            "--out" => a.out = Some(next()),
            other => panic!("unknown flag: {other}"),
        }
        i += 1;
    }
    a
}

fn main() {
    let args = parse_args();
    eprintln!(
        "=== SU(2) plaquette scan (heatbath + {} overrelax) ===\n  betas: {:?}\n  L: {:?}\n  sweeps: {} therm + {} meas (every {})\n  threads: {}",
        args.overrelax, args.betas, args.ells, args.therm, args.meas, args.interval, args.threads
    );

    let mut rows: Vec<String> = Vec::new();
    for &l in &args.ells {
        for &beta in &args.betas {
            let seed = args
                .seed
                .wrapping_add((l as u64).wrapping_mul(1_000_003))
                .wrapping_add((beta * 1000.0) as u64);
            let t0 = Instant::now();
            let r = run_mcmc(
                l, beta, args.therm, args.meas, args.interval, args.overrelax, seed, args.threads,
            );
            let secs = t0.elapsed().as_secs_f64();
            eprintln!(
                "  L={:>2} beta={:>4.2}  <P> = {:.6} +/- {:.6}   ({:.1}s)",
                l, beta, r.plaquette_mean, r.plaquette_stderr, secs
            );
            rows.push(format!(
                "  {{\"l\": {}, \"beta\": {}, \"n_therm\": {}, \"n_meas\": {}, \"meas_interval\": {}, \"n_overrelax\": {}, \"plaquette_mean\": {}, \"plaquette_stderr\": {}, \"threads\": {}, \"elapsed_seconds\": {:.3}}}",
                l, beta, args.therm, args.meas, args.interval, args.overrelax,
                r.plaquette_mean, r.plaquette_stderr, args.threads, secs
            ));
        }
    }

    let json = format!("{{\n \"points\": [\n{}\n ]\n}}\n", rows.join(",\n"));
    match &args.out {
        Some(path) => {
            std::fs::write(path, &json).expect("failed to write output JSON");
            eprintln!("\nJSON: {path}");
        }
        None => print!("{json}"),
    }
}
