# P11 window survival, beta=2.7, 24^3x32 — **MC/lit only, not proof**

Run: bin/p4run_p9 multilevel slab d=4, nsub {40,100}, interval 2, seed 2702, 1200 configs (therm 200), finished 2026-10-07 03:35:56 PT (32579 s).
Observable: exact padded anchor Y_j = timeslice spatial-plaquette sum, one-sided time box M=side. W = R_Y(s+1)/R_Y(s/2) (E1: interior pairs, matched-mean subtraction; E3d subtraction-free). σ: jackknife over bins of 10 configs (120 bins); binning stable from bin 2..40 (σW s=3 nsub=100: 0.016/0.016/0.015/0.014/0.013).
Step ratio c(k) = side·(1 − R_Y(k+1)/R_Y(k)), c_s2 = c(k=s/2 floor), θ_k=(R_Y(k+1)/R_Y(k))^(s/2+1).

| nsub | s | W (E1) | σ | z=W/σ | W E3d | c(0) | c(s/2) |
|---|---|---|---|---|---|---|---|
| 100 | 2 | 0.052 | 0.010 | 5.4 | -0.020(0.069) | 1.870(2) | 1.695(19) |
| 100 | 3 | 0.028 | 0.015 | 1.9 | 0.031(0.069) | 2.799(4) | 2.504(42) |
| 100 | 4 | 0.073 | 0.116 | 0.6 | 1.73(1.37) | 3.728(7) | 3.323(76) |
| 40 | 2 | 0.040 | 0.019 | 2.1 | -0.037(0.072) | 1.871(4) | 1.715(37) |
| 40 | 3 | 0.024 | 0.030 | 0.8 | -0.005(0.076) | 2.803(7) | 2.537(83) |
| 40 | 4 | 0.117 | 0.242 | 0.5 | 2.40(2.45) | 3.734(13) | 3.369(151) |

Sides 5,6 not produced by the measurement layout used here (report tooling covers s=2..4). Monotonicity c(k+1)−c(k): −10.3σ/−7.6σ/−2.8σ (nsub=100, s=2/3/4) — decreasing, no violation.
Level-0 direct (same chain) is uninformative (σ ≥ 0.2). s=3 is not yet resolved (z=1.9); extension P11x (same seed lineage, resumed from the P11 checkpoint, target 3300 cfg) is running.

Resources: 1085 samples; MemAvailable min 2337 MB / max 8687 MB; load1 max 7.64 mean 4.07; job RSS max 276 MB; nproc 8. Peak sampler events: one PAUSE at 00:07 PT (MemAvailable 2349 MB, above the 2 GB floor), resumed 00:10; thresholds then raised to PAUSE 5120/RESUME 5632 MB.
