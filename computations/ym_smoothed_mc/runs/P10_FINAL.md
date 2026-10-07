# P10 final: multilevel production on the exact Lean anchor Y_j — 2026-10-06 18:26 PT

**MC numerics only; not proof.**

Run: `runs/p10_ml_d4_b2.50_L16x32`, beta 2.5, 16³×32, multilevel slab d=4 (spatial links frozen on t%4==0), sub-update levels nsub=40 and 100 from the same level-0 configs, interval 2, seed 2601, 4 threads (throttled to 2 for ~10 min), 2400 configs, wall 13:21–18:26 PT (5.07 h). Median 7.46 s/config (level-0 0.20 s + sub-updates 7.26 s). Auto status/checkpoint: `P10_STATUS.md`, `P10_CHECKPOINT40.md` (15:17 PT). Detailed auto dump: `P10_FINAL_auto.md`. Step ratio: `P10_STEP_RATIO.md`.

Y_j = vacuum-centered sum of all unsmoothed spatial plaquettes on one timeslice, with one-sided time box M=side (the exact Lean padded anchor consumed by ExprStepRatio / 9d58a5df). Estimator: interior pairs only; E1 = matched pair-set mean subtraction; E3d = subtraction-free D(n)=R_Y(n)−R_Y(n+1) over all pairs (exact zero-mode cancellation; noisier). Jackknife over bins of 10 (240 bins).

## W(Y_j) vs side

| nsub | side | W E1 | W E3d | R_Y(s/2)/R_Y(0) | R_Y(s+1)/R_Y(0) | σ from 0 (E1) |
|---|---|---|---|---|---|---|
| **100** | **2** | **0.082(6)** | 0.044(35) | 0.099(1) | 0.008(1) | +13.7 |
| **100** | **3** | **0.038(11)** | 0.007(33) | 0.103(1) | 0.004(1) | **+3.5** |
| **100** | **4** | **0.041(67)** | 0.29(25) | 0.025(2) | 0.001(2) | +0.6 |
| 40 | 2 | 0.093(11) | 0.033(37) | 0.099(2) | 0.009(1) | +8.5 |
| 40 | 3 | 0.046(18) | 0.020(36) | 0.103(2) | 0.005(2) | +2.6 |
| 40 | 4 | 0.061(97) | 0.31(27) | 0.027(3) | 0.002(3) | +0.6 |

References (same ensemble / related):
- flow-loop ρ=1 W (p8_hi direct): 0.1678(88) / 0.1033(75) / 0.139(14) at sides 2/3/4
- direct Y_j (p8_hi, 5400 meas, E1/E3d): −0.08(11)/−0.015(63), 0.02(18)/−0.13(8), ill-defined
- P9 multilevel pilot (d=4, 534 cfg, nsub=40): 0.112(25), 0.037(49), 0.02(27)

## Binning check (σW E1 stable from bin=2 to bin=40)

| nsub | bin=2 | bin=5 | bin=10 | bin=20 | bin=40 |
|---|---|---|---|---|---|
| 100, σW s=2 | 0.007 | 0.007 | 0.006 | 0.007 | 0.006 |
| 100, σW s=3 | 0.012 | 0.011 | 0.011 | 0.010 | 0.010 |
| 40, σW s=2 | 0.011 | 0.012 | 0.011 | 0.011 | 0.011 |
| 40, σW s=3 | 0.018 | 0.019 | 0.018 | 0.018 | 0.019 |

No evidence of under-binned autocorrelation. Primary quote uses bin=10.

## Equal-cost gain vs direct (plaquette-only)

| nsub | VRF W s=2 | VRF W s=3 | cost/config (s) | h for ±0.02 at s=2 | h for ±0.03 at s=3 |
|---|---|---|---|---|---|
| 40 | 12.6 | 12.8 | 3.09 | 0.7 | 0.7 |
| 100 | 16.9 | 13.8 | 7.46 | 0.5 | 0.7 |

Going from 40→100 still raised the VRF ~1.3× at W, so nsub=100 is not fully saturated.

## E1 vs E3d at side 3 (reconciliation)

| | W E1 | W E3d | Δ (E1−E3d) |
|---|---|---|---|
| nsub=100 | 0.038(11) | 0.007(33) | 0.031(35) — consistent within 1σ |
| nsub=40 | 0.046(18) | 0.020(36) | 0.026(40) — consistent |

E3d is ~3× noisier (it includes frozen-boundary slices that are not sub-averaged) and is consistent with both E1 and with 0. **Accurate claim:** W(Y_j, s=3) is **positive at 3.5σ in E1** (0.038(11)); the subtraction-free E3d check is **unresolved** (0.007(33), only +0.2σ). E3d does not contradict E1; it is not precise enough to confirm the same confidence on its own.

## Does W fall off with side faster than the flow loop?

| side | W(Y_j) nsub=100 | flow ρ=1 W | ratio W_Y / W_flow |
|---|---|---|---|
| 2 | 0.082(6) | 0.168(9) | **0.49(5)** |
| 3 | 0.038(11) | 0.103(8) | **0.37(11)** |
| 4 | 0.041(67) | 0.139(14) | 0.3(5) (noise) |

Yes: at sides 2 and 3, W on the exact Lean anchor is **~2–3× smaller** than the flow-loop W, and the ratio itself falls from 0.49 to 0.37 (side 4 is consistent with that trend but unresolved). Relative to the ground-state-only floor computed in P9 with the n=1 overlap (0.19(4) at s=2), P10 sits ~2.7σ low; with the n=2 overlap floor (0.12(3)) it is 1.2σ low. The padded plaquette anchor therefore has a smaller survival fraction than the smoothed-loop expression anchor, consistent with a larger UV / excited-state contamination in Y_j (c(0)≈0.9·side; see step-ratio).

## Tension with the 37-min pilot (0.112(25) at s=2)

| | W(Y_j, s=2) E1 | N | σ |
|---|---|---|---|
| P9 pilot nsub=40 | 0.112(25) | 534 | — |
| P10 nsub=40 | 0.093(11) | 2400 | — |
| P10 nsub=100 | 0.082(6) | 2400 | — |
| pilot − P10(100) | 0.030(26) | | **1.2σ** |

The ~2σ tension quoted mid-run (pilot 0.112 vs then-current ~0.072–0.080) has collapsed to **1.2σ** once both runs are finished and the production error is ±0.006. The pilot's jackknife error (53 bins) is itself uncertain at the 30–40% level. **Verdict: consistent with statistics; no evidence of a systematic.** nsub=40 and nsub=100 within P10 also agree (0.093(11) vs 0.082(6), 0.9σ).

## Verdict

1. **Side 2:** W(Y_j) = 0.082(6), resolved well past ±0.02. Positive, ~2× below the flow-loop W, ~1σ below the n=2-overlap ground-state floor.
2. **Side 3 (key question):** W(Y_j) = 0.038(11) in E1 (**positive at 3.5σ**); subtraction-free E3d = 0.007(33) is **unresolved** and consistent with both E1 and 0. The pilot's 0.037(49) is confirmed by E1. Do **not** read this as an E3d confirmation of positivity.
3. **Side 4:** still unresolved (0.041(67)); denominator R_Y(2)/R_Y(0)=0.025(2). Nested two-level scheme remains the path for ±0.03 (see `P10_NESTED_SCOPE.md`).
4. Exact Lean anchor survival falls off with side faster than the flow loop (ratio ~0.5 → ~0.4).

## Resources (30-s sampler, 602 samples, 13:21–18:26 PT)

| | min | mean | max |
|---|---|---|---|
| MemAvailable (MB) | 2349 | 6528 | 9651 |
| load1 | 1.97 | 3.87 | 13.07 |
| job CPU (%) | — | 346 | 382 |
| job RSS (MB) | — | — | 84 |

Throttle/pause events (4):
- 13:35:00 PAUSE (MemAvailable 2349 MB) — 13:35:30 RESUME (6430 MB)
- 16:15:12 THROTTLE threads 4→2 (load1 9.41) — 16:25:43 RESTORE threads→4

21 samples at reduced threads; 1 sample paused. Lean headroom (~3 GiB) was respected except for one 30-s dip to 2.3 GB.
