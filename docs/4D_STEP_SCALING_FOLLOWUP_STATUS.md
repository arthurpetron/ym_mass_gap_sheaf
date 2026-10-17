# 4D step-scaling follow-up program — status (updated after each stage)

MC only; not a proof, not a bound. Started 2026-10-17 14:41 PDT. Runs on the Mac (darthurtron.local, 16 cores, 64 GiB), niced 19, single-threaded, <= 3 simulation processes alive, `run_guard.sh` (throttle to 1 process if load1 > 16, pause if free RAM < 15%), detached queue `run_queue.py` on `/Users/darthur/ym_numerics_runs/prod2/jobs_all.txt` (stages A, B(iii), C, D in this order; all checkpointed/resumable; stop with `touch /Users/darthur/ym_numerics_runs/GUARD_STOP` + `pkill -f run_queue.py`). Job list with seeds: `simulations/gf_step_scaling/results/followup/jobs_all.txt`.

## Status log
* 14:44 PDT: queue + guard launched (65 jobs). Free-field exact check done (see Stage A).
* 14:50 PDT: Stage A running (U(1) L=16 at 7 betas, high-beta U(1) at L=4..12). Stage B (i),(ii),(iv),(v),(vi) analysed on existing data (files `results/followup/B_*.md`); Stage B(iii) (c = 0.5) waits for new L=8 c=0.5 runs (queued after A). Interim B findings (details in the Stage B section when finished):
  * Dropping the coarsest pair 4->8 makes the c=0.3 / c=0.4 continuum shifts agree (u=2.0: 0.0641(33) vs 0.0705(58), 1.0 sigma); quadratic-in-x exact fit: 0.0675(45) vs 0.0723(78). The disagreement of the 3-pair linear fit is a coarse-pair (a/L = 1/4) artefact.
  * Plaquette-type E gives the same finest-pair shifts as the clover E (6->12: 0.0664(12) vs 0.0648(13) at u=1.3, c=0.3) with a much larger 4->8 cutoff effect (0.103 vs 0.077).
  * L and 2L ensembles are independent chains: series correlations are 0 within 1/sqrt(n) and full-vs-diagonal covariance changes the continuum error by < 1%; no benefit possible without coupled sampling.
  * Plaquette control variate: no gain at L >= 6 (|rho| <= 0.3, gain between -49% and +7% in jackknife), 20–35% variance gain only at L=4.
