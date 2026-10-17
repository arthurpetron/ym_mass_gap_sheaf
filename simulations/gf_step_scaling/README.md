# gf_step_scaling
SU(2) (and compact U(1) control) Wilson-action Monte Carlo on the periodic 4D torus with Wilson gradient flow; gradient-flow coupling and step-scaling analysis. **MC measurement only; never a proof or bound.** See `docs/4D_STEP_SCALING_PLAN.md` and `docs/4D_STEP_SCALING_RESULTS.md`.

Build: `CARGO_TARGET_DIR=/Users/darthur/ym_numerics_runs/target cargo build --release --offline`.
Run one ensemble: `su2gf --L 8 --beta 3.4 --therm 500 --nmeas 1200 --sep 5 --c 0.3,0.4 --out NAME` (resumes from `NAME.ckpt`).
Many jobs on the Mac: `run_queue.py JOBFILE OUTDIR MAXP` (nice 19, <= 4 procs) together with `run_guard.sh LOG` (throttle to one process when load1 > ncpu, pause when free RAM < 15%). Detach with a new session; plain `nohup ... &` is killed when the agent shell exits.
Analysis: `analysis/ensemble_table.py`, `analysis/stepscale.py RUNDIR OUTDIR --pairs 4:8 --norm lat|cont`, `analysis/u1_control.py`.
