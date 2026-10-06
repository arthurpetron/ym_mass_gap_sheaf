# P9 item 2: binning and tau_int for the exact-anchor W (p8_hi, 5400 meas after skip 600)

Jackknife error of W(Y_j, box M=side) and of R_x(1)/R_x(0), R_x(2)/R_x(0) (unboxed plaquette sum) vs bin size b. tau(b) = b·Var(bin means)/(2 Var) for the per-meas plaquette-sum mean <P> and for Q(n) at n = 2, 5.

| b | bins | σ W s=2 (E1) | σ W s=3 | σ W s=4 | σ R(1)/R(0) | σ R(2)/R(0) | σ W s=2 (E3d) | tau <P> | tau Q(2) | tau Q(5) |
|---|---|---|---|---|---|---|---|---|---|---|
| 1 | 5400 | 0.1137 | 0.1859 | 4.7208 | 0.00238 | 0.00241 | 0.0608 | 0.50 | 0.50 | 0.50 |
| 2 | 2700 | 0.1146 | 0.1875 | 4.7954 | 0.00237 | 0.00245 | 0.0613 | 0.58 | 0.58 | 0.58 |
| 5 | 1080 | 0.1148 | 0.1932 | 4.8848 | 0.00237 | 0.00250 | 0.0607 | 0.66 | 0.66 | 0.66 |
| 10 | 540 | 0.1129 | 0.1881 | 4.7629 | 0.00232 | 0.00247 | 0.0616 | 0.70 | 0.70 | 0.70 |
| 20 | 270 | 0.1149 | 0.1828 | 4.9300 | 0.00229 | 0.00255 | 0.0626 | 0.70 | 0.70 | 0.70 |
| 40 | 135 | 0.1091 | 0.1673 | 4.8543 | 0.00224 | 0.00255 | 0.0582 | 0.69 | 0.69 | 0.69 |
| 80 | 67 | 0.1036 | 0.1861 | 23.5296 | 0.00220 | 0.00218 | 0.0605 | 0.83 | 0.84 | 0.83 |
| 160 | 33 | 0.0902 | 0.1886 | 69.7430 | 0.00225 | 0.00203 | 0.0603 | 0.53 | 0.53 | 0.53 |

Plateau choice b = 20 (270 bins). W(Y_j) E1: s=2 -0.076(0.115), s=3 0.018(0.183), s=4 2.612(4.930).

## Measurements needed for σ(W) = 0.02 (σ ∝ N^-1/2 at fixed bin size; interval 2 sweeps, same cost per meas)

| side | σ(W) now | N now | N for ±0.02 | factor | wall time at 1.4 s/meas (2 threads) |
|---|---|---|---|---|---|
| 2 | 0.115 | 5400 | 1.78e+05 | 33x | 69 h (2.9 d) |
| 3 | 0.183 | 5400 | 4.51e+05 | 84x | 175 h (7.3 d) |
| 4 | 4.930 | 5400 | 3.28e+08 | 60763x | 127602 h (5316.7 d) |

Notes:
* tau_int of the per-meas plaquette-sum mean plateaus at ≈0.70 from b=10. The W errors are flat in b up to b=40, so b=20 (270 bins) is used for the final table (P9_P8HI_FINAL_ANCHOR.md).
* Side 4: the denominator R_Y(2) is consistent with 0 (R_Y(2)/R_Y(0) = 0.010(21)), so the ratio and its error are ill-defined (W = 2.6(49)). The '±0.02' count there is meaningless: it would need R_Y(2) resolved first. Only R_Y(5)/R_Y(0) = 0.026(22) is a usable number.
* Cost: p8_hi spends 1.4 s/meas mostly on flows for the comparison loops. A plaquette-only chain (2 sweeps per meas ≈ 0.25 s at 2 threads, plaquette measurement ~0.01 s) would need ≈ 1.8e5 × 0.26 s ≈ 13 h for ±0.02 at side 2 and ≈ 33 h at side 3, assuming the same per-meas variance.
