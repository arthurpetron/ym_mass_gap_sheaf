# P10 exact-anchor step ratio c(k) on Y_j from the multilevel data — 2026-10-06 18:26 PDT

**MC numerics only; not proof.** Tests the open Lean input `ExprStepRatio tr ρ k` (ρ_j R_j(k_j) ≤ R_j(k_j+1); BF4WilsonAllNomeExprStepRatioWindowSurvival.lean:232, consumed by 9d58a5df) on the exact padded anchor Y_j = timeslice spatial-plaquette sum (unit coefficients) with one-sided time box M=side.

run `runs/p10_ml_d4_b2.50_L16x32` (P10 production): 16^3x32, beta 2.5, multilevel d=4, nsub [40, 100], N=2400 configs, bins of 10. E1 = interior pairs + matched-mean subtraction; c_D = subtraction-free differenced correlator (all pairs). c(k) = side·(1 − R_Y(k+1)/R_Y(k)); θ_k = (R_Y(k+1)/R_Y(k))^(s/2+1); W = R_Y(s+1)/R_Y(s/2). mono = largest increase c(k+1)−c(k) in σ (jackknife of the difference; > +2 would flag a violation of monotonicity).

| nsub | side | bins | c(k=0) | c(k=1) | c(k=2) | mono (σ) | c_D(0) | c_D(s/2) | θ_0 | θ_{s/2} | W E1 | W E3d | R_Y(1)/R_Y(0) | R_Y(s/2)/R_Y(0) | R_Y(s+1)/R_Y(0) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 100 | 2 | 240 | 1.801(0.002) | 1.546(0.011) |  | -25.7 | 1.830(0.003) | 1.610(0.052) | 0.010(0.000) | 0.052(0.003) | 0.082(0.006) | 0.044(0.035) | 0.099(0.001) | 0.099(0.001) | 0.008(0.001) |
| 100 | 3 | 240 | 2.692(0.004) | 2.286(0.026) |  | -17.6 | 2.743(0.009) | 2.445(0.096) | 0.011(0.000) | 0.057(0.004) | 0.038(0.011) | 0.007(0.033) | 0.103(0.001) | 0.103(0.001) | 0.004(0.001) |
| 100 | 4 | 240 | 3.583(0.006) | 3.032(0.050) | 2.523(0.175) | -3.9 | 3.652(0.013) | 2.942(0.751) | 0.001(0.000) | 0.050(0.018) | 0.041(0.067) | 0.289(0.250) | 0.104(0.002) | 0.025(0.002) | 0.001(0.002) |
| 40 | 2 | 240 | 1.802(0.003) | 1.537(0.020) |  | -15.1 | 1.831(0.004) | 1.635(0.056) | 0.010(0.000) | 0.054(0.005) | 0.093(0.011) | 0.033(0.037) | 0.099(0.002) | 0.099(0.002) | 0.009(0.001) |
| 40 | 3 | 240 | 2.691(0.006) | 2.256(0.043) |  | -11.1 | 2.746(0.009) | 2.476(0.104) | 0.011(0.000) | 0.062(0.007) | 0.046(0.018) | 0.020(0.036) | 0.103(0.002) | 0.103(0.002) | 0.005(0.002) |
| 40 | 4 | 240 | 3.579(0.010) | 2.987(0.079) | 2.427(0.259) | -2.9 | 3.654(0.014) | 2.712(0.778) | 0.001(0.000) | 0.061(0.030) | 0.061(0.097) | 0.309(0.266) | 0.105(0.003) | 0.027(0.003) | 0.002(0.003) |

## Binning check (primary nsub): error of c(s/2) and c(0) vs bin size

| nsub | bin | bins | σc(0) s=2 | σc(s/2) s=2 | σc(0) s=3 | σc(s/2) s=3 | σc(0) s=4 | σc(s/2) s=4 |
|---|---|---|---|---|---|---|---|---|
| 100 | 5 | 480 | 0.002 | 0.012 | 0.004 | 0.027 | 0.007 | 0.179 |
| 100 | 10 | 240 | 0.002 | 0.011 | 0.004 | 0.026 | 0.006 | 0.175 |
| 100 | 20 | 120 | 0.002 | 0.012 | 0.004 | 0.027 | 0.007 | 0.162 |
| 100 | 40 | 60 | 0.002 | 0.011 | 0.004 | 0.024 | 0.006 | 0.151 |

## Comparison with P9 (beta 2.5, p8_hi 16^3x32 direct chain, 5400 meas; flow rho=1)

| side | operator | c(0) | c(s/2) |
|---|---|---|---|
| 2 | flow rho=1 loop | 1.3963(46) | 1.249(15) |
| 2 | Lean smoothed state (flow loop + box M=side) | 1.295(12) | 1.188(32) |
| 2 | Y_j direct chain (P9) | 1.811(18) | 1.78(18) |
| 2 | **Y_j multilevel nsub=100 (this run)** | 1.801(0.002) | 1.546(0.011) |
| 3 | flow rho=1 loop | 1.8087(66) | 1.625(16) |
| 3 | Lean smoothed state (flow loop + box M=side) | 1.665(21) | 1.565(46) |
| 3 | Y_j direct chain (P9) | 2.735(41) | 2.63(45) |
| 3 | **Y_j multilevel nsub=100 (this run)** | 2.692(0.004) | 2.286(0.026) |
| 4 | flow rho=1 loop | 2.2438(92) | 1.990(38) |
| 4 | Lean smoothed state (flow loop + box M=side) | 2.040(36) | 1.86(13) |
| 4 | Y_j direct chain (P9) | 3.641(75) | 1.2(24) |
| 4 | **Y_j multilevel nsub=100 (this run)** | 3.583(0.006) | 2.523(0.175) |
