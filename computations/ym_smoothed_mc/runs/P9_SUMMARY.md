# P9 summary (MC numerics only; not proof) — 2026-10-06

Files:
- item 1: `P9_P7_SECTOR_ADDENDUM.md`
- item 2: `P9_P8HI_FINAL_ANCHOR.md`, `P9_P8HI_BINNING.md`
- item 3: `P9_STEP_RATIO_FULL.md`
- item 4: `P9_POSITIVITY.md`
- item 5: `P9_P7_RAW_VS_SMOOTH.md`
- item 6: `P9_MULTILEVEL_PILOT.md`

Scripts: `ana/p9_sector.py`, `ana/p9_p8hi_bins.py`, `ana/p9_full.py`, `ana/p9_rawsmooth_p7.py`, `ana/p9_ml.py`, `p9_ml_run.sh`; `src/main.rs` adds `--ml-d`, `--ml-nsub`.

## 1. P7 Polyakov sector
- P7_FINAL did not split by sector.
- The dir-3 loop was negative in **236/240** meas, so a sign split or data-based symmetrization is impossible.
- By exact center symmetry, a symmetrized estimator equals the single-sector one for contractible loops.
- The relevant variable is |P3| (an ordered slow mode). Magnitude and stretch splits:
  - eps·side is stable, 2.5-2.8 (the Ls=48 vs 32 shift is not a sector artefact).
  - W differs between the two long stretches: 0.27(10) vs 0.52(9) (E3d 0.00(14) vs 0.52(14)). The quoted W error, 0.068, is probably about 1.5x too small.

## 2. p8_hi final: exact Y_j, beta 2.5, 16^3x32, 5400 meas, bin 20 (tau_int of <P> ≈ 0.7, plateau from b=10)
| side | Y_j R(1)/R(0) | Y_j R(s/2)/R(0) | Y_j R(s+1)/R(0) | **W(Y_j) E1** | **W(Y_j) E3d** | flow rho=1 W (E1/E3d) | flow+box W | f0_x | f0_Y(0) | ground-state-only W | m0 a (flow) |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 2 | 0.0931(95) | 0.0931(95) | −0.007(10) | −0.08(11) | −0.015(63) | 0.1678(88) / 0.164(15) | 0.179(22) | 0.088(4) (n=1), 0.057(10) (n=2) | 0.199(12) | 0.19(4) | 0.802(45) |
| 3 | 0.083(15) | 0.083(15) | 0.002(15) | 0.02(18) | −0.13(8) | 0.1033(75) / 0.091(11) | 0.135(27) | 0.0383(17), 0.035(12) | 0.104(7) | 0.063(15) | 0.747(34) |
| 4 | 0.084(20) | 0.010(21) | 0.026(22) | ill-defined (R_Y(2) ≈ 0) | — | 0.139(14) / 0.122(21) | 0.198(58) | 0.024(3), 0.012(7) | 0.082(10) | — | 0.644(47) |

- Unboxed plaquette sum: R_x(0) = 9.54(3)e-6 in loop units, R_x(1)/R_x(0) = 0.0775(23).
- **Measurements for ±0.02:**
  - side 2: 1.8e5 meas (33x the current count). At the p8_hi rate (1.4 s/meas incl. flows) that is ≈69 h; a plaquette-only chain (≈0.26 s/meas) would take ≈13 h.
  - side 3: 4.5e5 meas (≈33 h plaquette-only).
  - side 4: R_Y(2) must be resolved first.
- **Verdict:** W on Y_j is still not resolved. At side 2 it now sits LOW: −0.08(11) (E1), −0.015(63) (E3d). That is 2.3σ / 2.9σ below the flow-loop W and about 2σ below the ground-state-only expectation, c0·g0²·λ0^3/R_Y(1) = 0.19(4), or 0.12(3) using the n=2 overlap.
  - Since all spectral weights are ≥ 0, that expectation is a floor if c0 and λ0 are right. This is therefore a ~2σ hint that W(Y_j) is smaller than the overlap argument suggests (or that the factorization c0 is biased high).
  - It is not significant enough to call collapse. The multilevel estimator (item 6) can settle it in a few hours.

## 3. Step-ratio c(k) = side·(1 − R(k+1)/R(k))
- **Smoothed loop (rho=1), matched trajectory:** c(s/2) = 1.25 (side 2), 1.62-1.67 (3), 1.68-1.99 (4), 1.80(15) (6), 1.67(17) / 1.88(19) (8, Ls=32 / 48), 2.32(41) (10, not thermalized). c(0) = 1.40 → 2.66.
- **Exact Lean smoothed state of 9d58a5df** (one-sided box M=side of the centered expression, here ψ = flow loop): c(s/2) = 0.99-1.19, 1.32-1.57, 1.55-1.86, 2.03(59), 1.30(50)-1.89(68).
- **Bounded:** c(s/2) ≤ ≈2.3 at every side 2-10, with no growth. θ_k at k=s/2 ≈ 0.14-0.41, in line with the measured W ≈ 0.13-0.37 (θ ~ e^(−c/2) ≈ 0.3-0.5).
- **Monotonicity in k:** no increase beyond 2σ at sides 2-8 for any operator. Side 10 violates it (+2.3 to +2.6σ at rho 1.0-1.5, also with skip 85), the same thermalization / vacuum-subtraction flag as before.
- **Convexity bound** c(s/2) ≤ side·ln(R(s/4)/R(s/2))/(s/2 − s/4) holds everywhere it is defined.
  - The requested "4·R(s/4)/R(s/2)" is read as this log form: c(s/2) ≤ 4 ln(R(s/4)/R(s/2)), which the linear form dominates.
- **Padded plaquette anchor Y_j:** c(0) = 1.81, 2.73, 3.64 at side 2, 3, 4, i.e. ≈ 0.9·side, NOT bounded at k=0 (the H-ray caveat). c(s/2) = 1.78(18), 2.63(45), 1.2(24): noise-limited.

## 4. Hankel / Hausdorff positivity (d2710c09 forms; R normalized; Hankel N=2..4, m=0,1, l=0,1; CM l ≤ 4, n ≤ side+1)
- **Sides 2-8:** 15/696 Hankel and 9/1717 CM entries have z < −2. That is 2.2% and 0.5%, at or below the one-sided chance rate (2.3%); entries are correlated. The worst are −3.0σ (b2.70 side 5, CM l=4) and −2.9σ (b2.60 side 3, 2×2 Hankel), consistent with chance across ~2400 tests. **No evidence of bias at sides 2-8.**
- **Side 10:** 17/72 Hankel entries have z < −2, as low as −3.9σ: 8/12 at rho=1.5 (skip 0) and 5/12 at rho=1.5 (skip 85). These are log-convexity (2×2) and higher Hankel failures, a significant violation pointing again to slow-mode / vacuum-subtraction bias at side 10.

## 5. Raw vs smoothed on P7 Ls=48
- Cheap, done: the raw side-8 loop drowns at lag 2 (m_eff(0) = 3.16(27)).
- Smoothed m_eff at rho=1: 0.404(15) → 0.268(31) over n=0..4, falling slowly with no clean plateau, as at Ls=32.

## 6. Multilevel pilot (see `P9_MULTILEVEL_PILOT.md`)
- d=4, nsub=40, interior-pairs estimator. Equal-cost VRF vs direct is about 1–2 at n ≤ 2 and 7–30 at n ≥ 3. For W(Y_j) it is **11 (s=2) and 8 (s=3)**.
- The 37-min pilot gives W(Y_j, s=2) = **0.112(25)**.
- Hours to ±0.02: about **1 h (s=2)** and **4 h (s=3)** on 2 threads; side 4 about 100 h (denominator ≈ 0).
- Not launched. Plan: one run, d=4, nsub 40/100, 4 threads, about 3–4 h.
