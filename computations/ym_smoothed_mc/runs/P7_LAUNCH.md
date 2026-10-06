# P7 launch record: beta 2.95, 48^3 x 48, side 8 (larger-Ls rerun of b2.95_L32x48_s8)

## Run
- **Directory:** `runs/b2.95_L48x48_s8` (box: /workspace/ymmc/p4_smoothed). Launched 2026-10-06 06:09 PT with `setsid nohup bash p7_queue.sh`. p4run pid 794641; sampler `sampler_p7.sh` pid 794643.
- **Args:**
  - `--Ls 48 --Lt 48 --beta 2.95 --therm 1000 --therm-ckpt 100 --meas 240 --interval 4 --overrelax 4`
  - `--sides 7,8,9 --tflow 0,2.66667,6,10.66667,16.66667,24` (rho = 0, 0.5, 0.75, 1, 1.25, 1.5 at side 8; same set as Ls=32)
  - `--eps 0.05 --eps2 0.1 --tswitch2 2 --eps3 0.15 --seed 2953 --ckpt 5 --save-every 3 --save-dir runs/b2.95_L48x48_s8/cfg`
  - `--threads 4 --threads-file runs/b2.95_L48x48_s8/threads`
- **Speed (4 threads):**
  - Benchmark `runs/p7bench_b2.95_L48x48`, 3 meas: 81.4-82.0 s/meas.
  - Thermalization: about 4.4 s/sweep, so 1000 sweeps take about 74 min (ends about 07:23 PT).
  - Production: 240 × 82 s ≈ 5.5 h.
- **ETAs (PT):** auto-interim at 80 meas about 09:15; final about 12:55 (if not throttled).
- **Memory:** RSS is 0.98 GB during thermalization (links + geometry). Expected about 2.4 GB in the measurement phase, when the two flow buffers are allocated; the 3-meas benchmark lowered MemAvailable by about 2.2 GB. The sampler logs job_rss_MB.

## What changed in p4run (src/main.rs; the old binary is kept as bin/p4run_p6)
- `--therm-ckpt k` checkpoints every k thermalization sweeps. `--resume` continues thermalization if it was interrupted. Validated: interrupted and resumed with a thread change, the final config is bit-identical to an uninterrupted run, and records agree to 4e-15 (summation order only).
- Every measurement line now prints `th=<threads> O_s8=<operator mean at every level> P_last=[spatial Polyakov loops at the largest level]`, so drift is visible live.
- **Smeared spatial Polyakov loop:** the product of Ls spatially flowed links along x, y and z on every timeslice (smearing = the same spatial Wilson flow levels). The line means of P and P^2 per direction and level are appended to each record (header `"poly":6`). `ana/load.py:load_poly()` reads them.
- **Config saving:** `--save-every 3 --save-dir`. Every 3rd post-thermalization measurement config is written as **f32** (16-byte header with sweep and meas as u64 LE, then links [t][z][y][x][mu][a0..a3]). Re-unitarize on load. Each config is 339.7 MB, so 80 configs come to about 27 GB (108 GB free on /). Checked: an f32 config matches the f64 checkpoint to 3e-8.
- **Threads file:** `--threads-file f`. p4run re-reads f before every sweep and measurement, clamped to 1..launch threads, and logs `threads a -> b`.
- **Linear smearing (f):** `--linear-alpha a --linear-steps n1,n2,...` adds levels after the flow levels (header `linear_alpha`, `linear_steps`). Self-test: `p4run --selftest-linear`.

## Throttle (sampler_p7.sh, 30 s samples)
- **Drop to 3 threads** (writes `3` to the threads file; p4run picks it up at the next sweep, within about 5 s): immediately if MemAvailable < 2500 MB, or if load1 > 7 for 2 consecutive samples.
- **Restore 4 threads:** when MemAvailable > 3500 MB and load1 < 5.5 for 20 consecutive samples (10 min).
- **Memory emergency** (thread count does not free memory): SIGSTOP if MemAvailable < 1200 MB, SIGCONT when it is above 2000 MB.
- Every action is logged in `resources.log` as `# THROTTLE` / `# RESTORE` / `# MEM ...`.
- **Manual override:** `echo 3 > runs/b2.95_L48x48_s8/threads`.

## Auto-interim / final
`p7_queue.sh` polls every 5 min. At ≥ 80 complete records it runs `ana/p7_interim.py`, which writes `runs/P7_INTERIM.md`. That file contains:
- the thermalization discard, chosen as the first k meas where half-vs-half < 1.5σ and total linear drift < 2σ;
- W (E1, E3f, E3d), eps·s, eps_shift·s and R(s)/R(0) per rho, alongside the Ls=32 values;
- tau_int at Ls=48 vs Ls=32, and m_eff;
- the Polyakov history (mean |P|, sign changes, block maxima, correlation with <O>);
- resources (min/mean/max).

At the end the queue writes `runs/P7_FINAL_auto.md`.

## Restart after an interruption
`setsid nohup bash p7_queue.sh --resume > runs/p7_queue.log 2>&1 &` resumes from data.ckpt, in either the thermalization or the measurement phase.
