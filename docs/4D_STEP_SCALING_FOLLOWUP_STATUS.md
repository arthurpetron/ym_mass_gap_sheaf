# 4D step-scaling follow-up program — status (updated after each stage)

MC only; not a proof, not a bound. Started 2026-10-17 14:41 PDT. Runs on the Mac (darthurtron.local, 16 cores, 64 GiB), niced 19, single-threaded, <= 3 simulation processes alive, `run_guard.sh` (throttle to 1 process if load1 > 16, pause if free RAM < 15%), detached queue `run_queue.py` on `/Users/darthur/ym_numerics_runs/prod2/jobs_all.txt` (stages A, B(iii), C, D in this order; all checkpointed/resumable; stop with `touch /Users/darthur/ym_numerics_runs/GUARD_STOP` + `pkill -f run_queue.py`). Job list with seeds: `simulations/gf_step_scaling/results/followup/jobs_all.txt`.

## Status log
* 14:44 PDT: queue + guard launched (65 jobs). Free-field exact check done (see Stage A).
