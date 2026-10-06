# P9 step-ratio constant c(k) = side*(1 - R(k+1)/R(k)) — 2026-10-06 11:32 PDT

Source: existing P5/P6 effective masses (runs/p6/*.json); c(k) = side*(1-exp(-m_eff(k))), error by linear propagation.
Lean consumer: `expr_windowSurvivalFrom_of_stepRatio_anyC` (9cb9f1e2) needs side_j*(1-rho_j) <= c <= C at ONE lag k_j <= side_j/2.
Because R is log-convex, R(k+1)/R(k) is nondecreasing in k, so the most favorable admissible lag is k = side/2.

**Caveat:** MC operators only (rho = flow radius / side; rho=0 is the raw loop). NOT the exact Lean anchor Y_j, whose W is still unresolved (P8). Numerics, not proof.

| beta | side | rho | c(k=0) | c(k=1) | c(k=2) | c(k=3) | c(k=4) | c(k=5) |
|---|---|---|---|---|---|---|---|---|
| 2.5 | 2 | 0.00 | 1.75(0.01) | 1.41(0.11) |  |  |  |  |
| 2.5 | 2 | 0.50 | 1.61(0.01) | 1.34(0.07) |  |  |  |  |
| 2.5 | 2 | 1.00 | 1.40(0.02) | 1.24(0.05) |  |  |  |  |
| 2.5 | 2 | 1.50 | 1.24(0.02) | 1.10(0.04) |  |  |  |  |
| 2.6 | 3 | 0.00 | 2.68(0.02) | 2.07(0.26) |  |  |  |  |
| 2.6 | 3 | 0.50 | 2.21(0.02) | 1.98(0.08) |  |  |  |  |
| 2.6 | 3 | 1.00 | 1.79(0.02) | 1.67(0.05) |  |  |  |  |
| 2.6 | 3 | 1.50 | 1.53(0.02) | 1.43(0.05) |  |  |  |  |
| 2.7 | 4 | 0.00 | 3.61(0.03) | 3.70(0.40) | 1.27(4.51) |  |  |  |
| 2.7 | 4 | 0.50 | 2.69(0.04) | 2.33(0.09) | 1.97(0.17) |  |  |  |
| 2.7 | 4 | 1.00 | 2.08(0.03) | 1.78(0.06) | 1.64(0.09) |  |  |  |
| 2.7 | 4 | 1.50 | 1.65(0.03) | 1.47(0.05) | 1.37(0.07) |  |  |  |
| 2.85 | 6 | 0.00 | 5.72(0.04) | 5.64(?) | -27.59(?) | 1.63(3.13) |  |  |
| 2.85 | 6 | 0.50 | 3.26(0.04) | 3.07(0.08) | 2.68(0.16) | 2.23(0.33) |  |  |
| 2.85 | 6 | 1.00 | 2.37(0.04) | 2.19(0.06) | 1.95(0.09) | 1.82(0.14) |  |  |
| 2.85 | 6 | 1.50 | 1.73(0.05) | 1.57(0.06) | 1.49(0.07) | 1.45(0.10) |  |  |
| 2.95 | 8 | 0.00 | 7.99(?) | n/a | n/a | 4.61(?) | n/a |  |
| 2.95 | 8 | 0.50 | 3.55(0.06) | 3.18(0.12) | 2.72(0.21) | 2.50(0.24) | 2.41(0.31) |  |
| 2.95 | 8 | 1.00 | 2.36(0.09) | 2.09(0.11) | 1.97(0.15) | 1.76(0.15) | 1.67(0.17) |  |
| 2.95 | 8 | 1.50 | 1.75(0.08) | 1.62(0.10) | 1.60(0.11) | 1.61(0.14) | 1.57(0.16) |  |
| 3.0 | 10 | 0.00 | 9.90(0.08) | n/a | 5.95(6.80) | 1.86(28.70) | n/a | n/a |
| 3.0 | 10 | 0.50 | 3.55(0.10) | 3.22(0.13) | 2.95(0.20) | 2.80(0.26) | 2.90(0.37) | 2.96(0.57) |
| 3.0 | 10 | 1.00 | 2.06(0.09) | 2.02(0.10) | 2.05(0.13) | 2.10(0.18) | 2.28(0.27) | 2.32(0.41) |
| 3.0 | 10 | 1.50 | 1.68(0.08) | 1.78(0.10) | 1.93(0.14) | 2.10(0.21) | 2.32(0.32) | 2.36(0.46) |

## Reading
* Smoothed loop (rho ~ 1): c(k) stays about 1.2-2.4 at every measured lag k <= side/2 for sides 2-10, with no growth in side. So on the smoothed operator the step-ratio input looks satisfied with C = 3 (theta_C = 2^-8, c0 = 2^9), consistent with eps*side ~ 2.
* Raw loop (rho = 0): c(0) ~ side (1.75, 2.68, 3.61, 5.72, 7.99, 9.90) and larger lags are noise. This is consistent with the 9d58a5df docstring caveat that the lag-0 H-ray version on raw slab vectors is vacuous.
* Consistency check: log-convexity forces c(k) to be NONINCREASING in k. Sides 2-8 obey this. Side 10 (beta 3.0) rises with k at rho 1.0-1.5 (e.g. 1.68(8) -> 2.36(46) at rho 1.5, about 1.5 sigma), another sign that side 10 is not thermalized (P6) and that its streams disagree (WINDOW_SURVIVAL_s10_streamB, slow modes / vacuum subtraction). Read that row loosely.
* Nothing here touches the exact Lean anchor, the physical box, or the gap branch.
