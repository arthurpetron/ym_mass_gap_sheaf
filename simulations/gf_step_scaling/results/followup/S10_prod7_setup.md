# S10 — prod7 (full S9 design) setup, L32 probe, tuning in progress (2026-10-21 ~02:30 PDT)

MC only; no results yet.
**L32 probe** (β=3.44, twisted, cold, therm 20, 10 meas, sep 10, c=0.3/0.4 flows; 1 core, nice 19, ran alongside 2 tuning jobs, load1 6.7–11.9):
986 s real / 976 s user. The marginal rate is **97 s per unit** (10 sweeps + 1 flow; meas 5→10 took 487 s). That is 5.4× L24 (18.09 s), above the 76 s assumed in S9.
**Max RSS 916 MB** (peak footprint 657 MB), so 3 L32 processes need < 3 GB.
**Revised cost:** at L32 4×300 meas the full design would be ≈ 234 CPU-h, over the 230 cap. **L32 chains are therefore set to 4 × 280 meas** (1120 per u, 93% of S9).
* L32 per u: 33.4 CPU-h; × 6 u = 200.5.
* Rest: R1 (u = 3.6, 4.5; 8→16, 12→24) 14.4, L16(β16) × 6 = 4.0, tuning ≈ 2.1, probe 0.27.
* **Total ≈ 221 CPU-h.**
Tuning: 20 jobs (jobs7_tune.txt; L16 200 meas, L12/L8 300 meas). Phase 2 job generation and order: prod7_setup/mk_prod.py (R1 first, then 16→32). Resume instructions: prod7_setup/RESUME.md. Q is logged per configuration in the csv (Q column at each flow time).
