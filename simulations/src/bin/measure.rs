//! Combined measurement driver: runs ONE heatbath+overrelax chain and measures
//! both the 0++/2++ glueball correlation matrix and the Wilson-loop (string
//! tension) grid on every collected config, emitting the same two JSON schemas
//! the Python pipeline already consumes (`glueball-*.json`, `sigma-*.json`).
//!
//! Versus the separate `glueball` + `string_tension` binaries this:
//!   * thermalizes once and sweeps once for both observables (1 chain, not 2);
//!   * checkpoints to disk/GCS so a preempted (Spot) task resumes instead of
//!     restarting -- and the partial JSONs are rewritten at every checkpoint,
//!     so a run can be analyzed live;
//!   * is meant to be sharded: launch K copies with distinct seeds, each over
//!     meas/K sweeps, then merge their bins with
//!     `computations/long_runs/merge_shards.py`.
//!
//! Usage (one shard):
//!   measure --L 24 --beta 2.5 --therm 12000 --meas 125000 --interval 5 \
//!       --overrelax 4 --smear-levels 0,8,16,24,32 --smear-alpha 0.5 \
//!       --rmax 12 --tmax 12 --sigma-smear 4 --bins 8 --seed 104 \
//!       --shard 0 --nshards 8 \
//!       --checkpoint /mnt/disks/out/ckpt-L24-b2.5-s0.bin \
//!       --ckpt-secs 300 \
//!       --out-glueball /mnt/disks/out/glueball-L24-b2.5-s0.json \
//!       --out-sigma    /mnt/disks/out/sigma-L24-b2.5-s0.json

use ym_simulations::{measure_combined, CombinedParams, GlueballData, StringTensionData};

fn fmt_vec(v: &[f64]) -> String {
    v.iter().map(|x| format!("{x}")).collect::<Vec<_>>().join(", ")
}

fn corr_to_json(c: &[Vec<Vec<f64>>]) -> String {
    let mut s = String::from("[");
    for (i, row) in c.iter().enumerate() {
        if i > 0 {
            s.push_str(", ");
        }
        s.push('[');
        for (j, series) in row.iter().enumerate() {
            if j > 0 {
                s.push_str(", ");
            }
            s.push_str(&format!("[{}]", fmt_vec(series)));
        }
        s.push(']');
    }
    s.push(']');
    s
}

fn bin_corr_to_json(b: &[Vec<Vec<Vec<f64>>>]) -> String {
    let mut s = String::from("[");
    for (bi, mat) in b.iter().enumerate() {
        if bi > 0 {
            s.push_str(", ");
        }
        s.push_str(&corr_to_json(mat));
    }
    s.push(']');
    s
}

fn bin_op_to_json(b: &[Vec<f64>]) -> String {
    b.iter().map(|row| format!("[{}]", fmt_vec(row))).collect::<Vec<_>>().join(", ")
}

fn grid_to_json(g: &[Vec<f64>]) -> String {
    let mut rows = String::from("[");
    for (ri, row) in g.iter().enumerate() {
        if ri > 0 {
            rows.push_str(", ");
        }
        rows.push_str(&format!("[{}]", fmt_vec(row)));
    }
    rows.push(']');
    rows
}

/// Provenance fields appended to every emitted JSON so the merge tool / a human
/// can see which shard a partial belongs to.  Unknown keys are ignored by the
/// Python loaders.
fn provenance(seed: u64, shard: usize, nshards: usize) -> String {
    format!("\"seed\": {seed}, \"shard\": {shard}, \"n_shards\": {nshards}")
}

fn glueball_json(
    g: &GlueballData,
    interval: usize,
    elapsed: f64,
    seed: u64,
    shard: usize,
    nshards: usize,
) -> String {
    let levels_json =
        g.smear_levels.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", ");
    let counts_json =
        g.bin_counts.iter().map(|c| c.to_string()).collect::<Vec<_>>().join(", ");
    format!(
        "{{\n  \"l\": {}, \"beta\": {}, \"n_therm\": {}, \"n_collected\": {},\n  \"smear_levels\": [{}], \"smear_alpha\": {}, \"n_overrelax\": {}, \"threads\": {},\n  \"meas_interval\": {}, \"elapsed_seconds\": {:.3}, {},\n  \"mean_op\": [{}],\n  \"corr\": {},\n  \"n_bins\": {}, \"bin_counts\": [{}],\n  \"bin_op_sum\": [{}],\n  \"bin_corr_sum\": {},\n  \"mean_op_E\": [{}],\n  \"corr_E\": {},\n  \"bin_op_E_sum\": [{}],\n  \"bin_corr_E_sum\": {}\n}}\n",
        g.l, g.beta, g.n_therm, g.n_collected,
        levels_json, g.smear_alpha, g.overrelax, g.threads,
        interval, elapsed, provenance(seed, shard, nshards),
        fmt_vec(&g.mean_op),
        corr_to_json(&g.corr),
        g.n_bins, counts_json,
        bin_op_to_json(&g.bin_op_sum),
        bin_corr_to_json(&g.bin_corr_sum),
        fmt_vec(&g.mean_op_E),
        corr_to_json(&g.corr_E),
        bin_op_to_json(&g.bin_op_E_sum),
        bin_corr_to_json(&g.bin_corr_E_sum),
    )
}

fn sigma_json(
    s: &StringTensionData,
    interval: usize,
    elapsed: f64,
    seed: u64,
    shard: usize,
    nshards: usize,
) -> String {
    let counts_json =
        s.bin_counts.iter().map(|c| c.to_string()).collect::<Vec<_>>().join(", ");
    let bin_w_json =
        s.bin_w_sum.iter().map(|m| grid_to_json(m)).collect::<Vec<_>>().join(", ");
    format!(
        "{{\n  \"l\": {}, \"beta\": {}, \"n_therm\": {}, \"n_collected\": {},\n  \"r_max\": {}, \"t_max\": {}, \"smear_steps\": {}, \"smear_alpha\": {}, \"n_overrelax\": {}, \"threads\": {},\n  \"meas_interval\": {}, \"elapsed_seconds\": {:.3}, {},\n  \"w\": {},\n  \"n_bins\": {}, \"bin_counts\": [{}],\n  \"bin_w_sum\": [{}]\n}}\n",
        s.l, s.beta, s.n_therm, s.n_collected,
        s.r_max, s.t_max, s.smear_steps, s.smear_alpha, s.overrelax, s.threads,
        interval, elapsed, provenance(seed, shard, nshards),
        grid_to_json(&s.w),
        s.n_bins, counts_json, bin_w_json,
    )
}

fn main() {
    // Defaults: a quick smoke configuration.
    let mut l = 8usize;
    let mut beta = 2.4f64;
    let mut therm = 500usize;
    let mut meas = 4000usize;
    let mut interval = 5usize;
    let mut overrelax = 4usize;
    let mut smear_levels = vec![0usize, 8, 16, 24, 32];
    let mut smear_alpha = 0.5f64;
    let mut rmax = 4usize;
    let mut tmax = 4usize;
    let mut sigma_smear = 4usize;
    let mut bins = 8usize;
    let mut seed = 0u64;
    let mut threads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1);
    let mut out_glueball: Option<String> = None;
    let mut out_sigma: Option<String> = None;
    let mut checkpoint: Option<String> = None;
    let mut ckpt_configs = 0usize;
    let mut ckpt_secs = 0f64;
    let mut max_collect = 0usize;
    let mut shard = 0usize;
    let mut nshards = 1usize;

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
            "--rmax" => rmax = val().parse().unwrap(),
            "--tmax" => tmax = val().parse().unwrap(),
            "--sigma-smear" => sigma_smear = val().parse().unwrap(),
            "--bins" => bins = val().parse().unwrap(),
            "--seed" => seed = val().parse().unwrap(),
            "--threads" => threads = val().parse().unwrap(),
            "--out-glueball" => out_glueball = Some(val()),
            "--out-sigma" => out_sigma = Some(val()),
            "--checkpoint" => checkpoint = Some(val()),
            "--ckpt-configs" => ckpt_configs = val().parse().unwrap(),
            "--ckpt-secs" => ckpt_secs = val().parse().unwrap(),
            "--max-collect" => max_collect = val().parse().unwrap(),
            "--shard" => shard = val().parse().unwrap(),
            "--nshards" => nshards = val().parse().unwrap(),
            other => panic!("unknown flag: {other}"),
        }
    }
    smear_levels.sort_unstable();
    smear_levels.dedup();

    let p = CombinedParams {
        l,
        beta,
        n_therm: therm,
        n_meas: meas,
        meas_interval: interval,
        n_overrelax: overrelax,
        smear_levels: smear_levels.clone(),
        smear_alpha,
        r_max: rmax,
        t_max: tmax,
        sigma_smear,
        n_bins: bins,
        seed,
        threads,
    };

    eprintln!(
        "=== combined measure (L={l}, beta={beta}, shard {shard}/{nshards}, seed={seed}) ===\n  {therm} therm + {meas} meas (every {interval}), {overrelax} overrelax, smear {smear_levels:?}@{smear_alpha}\n  sigma: Rmax={rmax} Tmax={tmax} smear={sigma_smear}; {bins} bins, {threads} threads"
    );
    if let Some(cp) = &checkpoint {
        eprintln!("  checkpoint: {cp}  (every {ckpt_configs} configs / {ckpt_secs}s)");
    }

    // Live progress: rewrite the partial JSONs at every checkpoint so the run is
    // analyzable mid-flight, and so a preemption loses at most one interval.
    let og = out_glueball.clone();
    let os = out_sigma.clone();
    let on_progress = |g: &GlueballData, s: &StringTensionData, elapsed: f64| {
        if let Some(path) = &og {
            let _ = std::fs::write(path, glueball_json(g, interval, elapsed, seed, shard, nshards));
        }
        if let Some(path) = &os {
            let _ = std::fs::write(path, sigma_json(s, interval, elapsed, seed, shard, nshards));
        }
        eprintln!("  [progress] collected {} configs, {:.1}s elapsed", g.n_collected, elapsed);
    };

    let (g, s, elapsed, finished) = measure_combined(
        &p,
        checkpoint.as_deref(),
        ckpt_configs,
        ckpt_secs,
        max_collect,
        on_progress,
    );

    eprintln!(
        "  {} {} configs in {:.1}s",
        if finished { "FINISHED" } else { "STOPPED at" },
        g.n_collected,
        elapsed
    );

    // Final write.
    let gj = glueball_json(&g, interval, elapsed, seed, shard, nshards);
    let sj = sigma_json(&s, interval, elapsed, seed, shard, nshards);
    match &out_glueball {
        Some(path) => {
            std::fs::write(path, &gj).expect("write glueball json");
            eprintln!("  glueball JSON: {path}");
        }
        None => print!("{gj}"),
    }
    match &out_sigma {
        Some(path) => {
            std::fs::write(path, &sj).expect("write sigma json");
            eprintln!("  sigma JSON: {path}");
        }
        None => print!("{sj}"),
    }

    // Non-zero exit if we stopped early (lets the launcher distinguish a
    // budget-stop from a completed shard).
    if !finished {
        std::process::exit(3);
    }
}
