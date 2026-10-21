# prod7 resume (S9 full design)
Phase 1 (running/started 2026-10-21 02:09 PDT): guard (run_guard.sh -> resource_guard7.log), L32 probe (probe_L32_b3.44, /usr/bin/time -l -> probe32.time), tuning queue jobs7_tune.txt (maxp 2).
If interrupted: relaunch `python3 ../launch_detached.py queue7_tune.nohup python3 <G>/run_queue.py jobs7_tune.txt /Users/darthur/ym_numerics_runs/prod7 3` (resumes from .ckpt; finished jobs are no-ops), and the guard if not running.
Phase 2 (after all 20 tune_*.stderr show meas=N/N): `python3 mk_prod.py` (check betas, max|Q|), then `python3 mk_prod.py --write` and launch
`python3 ../launch_detached.py queue7_prod.nohup python3 <G>/run_queue.py jobs7_prod.txt /Users/darthur/ym_numerics_runs/prod7 3` (+ guard). Order: R1 (u=3.6,4.5; 8->16, 12->24) first, then 16->32.
<G> = /Users/darthur/Dore Dropbox/Arthur Petron/codex/ym_mass_gap_sheaf/simulations/gf_step_scaling
L32 chains reduced 300->280 meas (measured L32 97 s/unit keeps total under 230 CPU-h cap)
