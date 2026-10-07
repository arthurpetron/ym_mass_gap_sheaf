# P10 exact-anchor step ratio c(k) on Y_j from the multilevel data — 2026-10-07 03:37 PDT

**MC numerics only; not proof.** Tests the open Lean input `ExprStepRatio tr ρ k` (ρ_j R_j(k_j) ≤ R_j(k_j+1); BF4WilsonAllNomeExprStepRatioWindowSurvival.lean:232, consumed by 9d58a5df) on the exact padded anchor Y_j = timeslice spatial-plaquette sum (unit coefficients) with one-sided time box M=side.

run `runs/p11_ml_d4_b2.70_L24x32` P11 final 1200 cfg: 24^3x32, beta 2.7, multilevel d=4, nsub [40, 100], N=1200 configs, bins of 10. E1 = interior pairs + matched-mean subtraction; c_D = subtraction-free differenced correlator (all pairs). c(k) = side·(1 − R_Y(k+1)/R_Y(k)); θ_k = (R_Y(k+1)/R_Y(k))^(s/2+1); W = R_Y(s+1)/R_Y(s/2). mono = largest increase c(k+1)−c(k) in σ (jackknife of the difference; > +2 would flag a violation of monotonicity).

| nsub | side | bins | c(k=0) | c(k=1) | c(k=2) | mono (σ) | c_D(0) | c_D(s/2) | θ_0 | θ_{s/2} | W E1 | W E3d | R_Y(1)/R_Y(0) | R_Y(s/2)/R_Y(0) | R_Y(s+1)/R_Y(0) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 100 | 2 | 120 | 1.870(0.002) | 1.695(0.019) |  | -10.3 | 1.882(0.005) | 1.804(0.106) | 0.004(0.000) | 0.023(0.003) | 0.052(0.010) | -0.020(0.069) | 0.065(0.001) | 0.065(0.001) | 0.003(0.001) |
| 100 | 3 | 120 | 2.799(0.004) | 2.504(0.042) |  | -7.6 | 2.829(0.012) | 2.761(0.216) | 0.004(0.000) | 0.027(0.005) | 0.028(0.015) | 0.031(0.069) | 0.067(0.001) | 0.067(0.001) | 0.002(0.001) |
| 100 | 4 | 120 | 3.728(0.007) | 3.323(0.076) | 2.568(0.330) | -2.8 | 3.768(0.018) | -1.227(1.703) | 0.000(0.000) | 0.046(0.032) | 0.073(0.116) | 1.728(1.371) | 0.068(0.002) | 0.012(0.002) | 0.001(0.001) |
| 40 | 2 | 120 | 1.871(0.004) | 1.715(0.037) |  | -4.6 | 1.884(0.006) | 1.820(0.109) | 0.004(0.000) | 0.020(0.005) | 0.040(0.019) | -0.037(0.072) | 0.065(0.002) | 0.065(0.002) | 0.003(0.001) |
| 40 | 3 | 120 | 2.803(0.007) | 2.537(0.083) |  | -3.5 | 2.832(0.013) | 2.837(0.236) | 0.004(0.000) | 0.024(0.008) | 0.024(0.030) | -0.005(0.076) | 0.066(0.002) | 0.066(0.002) | 0.002(0.002) |
| 40 | 4 | 120 | 3.734(0.013) | 3.369(0.151) | 2.639(0.718) | -1.2 | 3.777(0.019) | -1.053(2.274) | 0.000(0.000) | 0.039(0.062) | 0.117(0.242) | 2.396(2.447) | 0.067(0.003) | 0.010(0.003) | 0.001(0.003) |

## Binning check (primary nsub): error of c(s/2) and c(0) vs bin size

| nsub | bin | bins | σc(0) s=2 | σc(s/2) s=2 | σc(0) s=3 | σc(s/2) s=3 | σc(0) s=4 | σc(s/2) s=4 |
|---|---|---|---|---|---|---|---|---|
| 100 | 5 | 240 | 0.002 | 0.020 | 0.004 | 0.043 | 0.007 | 0.347 |
| 100 | 10 | 120 | 0.002 | 0.019 | 0.004 | 0.042 | 0.007 | 0.330 |
| 100 | 20 | 60 | 0.002 | 0.019 | 0.004 | 0.039 | 0.007 | 0.319 |
| 100 | 40 | 30 | 0.002 | 0.021 | 0.004 | 0.040 | 0.007 | 0.295 |

## Comparison with P9 (beta 2.5, p8_hi 16^3x32 direct chain, 5400 meas; flow rho=1)

| side | operator | c(0) | c(s/2) |
|---|---|---|---|
| 2 | flow rho=1 loop | 1.3963(46) | 1.249(15) |
| 2 | Lean smoothed state (flow loop + box M=side) | 1.295(12) | 1.188(32) |
| 2 | Y_j direct chain (P9) | 1.811(18) | 1.78(18) |
| 2 | **Y_j multilevel nsub=100 (this run)** | 1.870(0.002) | 1.695(0.019) |
| 3 | flow rho=1 loop | 1.8087(66) | 1.625(16) |
| 3 | Lean smoothed state (flow loop + box M=side) | 1.665(21) | 1.565(46) |
| 3 | Y_j direct chain (P9) | 2.735(41) | 2.63(45) |
| 3 | **Y_j multilevel nsub=100 (this run)** | 2.799(0.004) | 2.504(0.042) |
| 4 | flow rho=1 loop | 2.2438(92) | 1.990(38) |
| 4 | Lean smoothed state (flow loop + box M=side) | 2.040(36) | 1.86(13) |
| 4 | Y_j direct chain (P9) | 3.641(75) | 1.2(24) |
| 4 | **Y_j multilevel nsub=100 (this run)** | 3.728(0.007) | 2.568(0.330) |
