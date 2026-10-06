# P7 (f): linear unprojected spatial staple smearing — implementation and validation (2026-10-06)

Code: `src/main.rs` `linear_smear_step` (V = (1-a) U + (a/4) Σ 4 spatial staples; no exp/renorm; time links copied). Flags `--linear-alpha`, `--linear-steps` (cumulative; levels appended after flow levels). Full linear re-run NOT launched (on hold).

## (i) Multilinearity / positive-combination check (`p4run --selftest-linear`, 4^3x4 hot random config, alpha=0.37)
- **Link level:** the code's V after 1 step equals Σ w·path over 5 explicit unsmoothed paths per link, with max residual 2.2e-16. After 2 steps it equals Σ over 505 paths per link, max residual 1.6e-15. All weights are positive (min 7.3e-5).
- **loops() level:** loops() on 1-step smeared links, for sides 1 (all 4 timeslices × 3 planes) and 2 (t=0 × 3 planes), was compared with brute-force enumeration of all 5^(4·side) choices per loop: 75,480,000 explicit terms, each the (1/2)Tr of an unsmoothed closed Wilson loop with a positive weight. Max |diff| = 8.8e-17 (relative ≤ 2e-13). 0 non-positive weights. **PASS** (full output: `runs/p7/selftest_linear.txt`).
- n=3 at link level (about 5e8 terms per link) is infeasible to enumerate. A first attempt was OOM-killed on the box at 11 GB, and only that test process was killed.

## (ii) 16^3x32, beta=2.5, side 2: linear vs spatial Wilson flow on the SAME configs
800 meas, interval 2, first 80 discarded, bins of 8, 2 threads, about 9 min per run. Both runs used seed 2501, so the flow rows are identical across the two tables.
| level | <O> (raw scale) | W E1 | W E3f | W E3d | eps*s | R(s)/R(0) | m_eff(0) | m_eff(1) | m_eff(2) | tau(O) b16 |
|---|---|---|---|---|---|---|---|---|---|---|
| flow t=0 (rho=0.00) | 0.258 | 0.080(50) | 0.045(95) | 0.088(91) | 1.749(14) | 0.0328(62) | 2.077(56) | 1.34(19) | 1.19(64) | 0.68 |
| flow t=0.375 (rho=0.75) | 0.7717 | 0.133(28) | 0.086(46) | 0.115(48) | 1.512(13) | 0.0884(68) | 1.411(28) | 1.015(70) | 1.00(20) | 0.92 |
| flow t=0.66667 (rho=1.00) | 0.8835 | 0.142(25) | 0.098(42) | 0.134(43) | 1.413(12) | 0.1140(71) | 1.227(21) | 0.945(55) | 1.01(16) | 1.07 |
| linear a=0.5 n=3 (rho_eq=0.75) | 0.005376 | 0.102(46) | -0.01(11) | 0.23(10) | 1.777(12) | 0.0287(67) | 2.193(53) | 1.36(23) | 0.92(45) | 0.72 |
| linear a=0.5 n=4 (rho_eq=0.87) | 0.0001711 | 0.102(52) | -0.03(13) | 0.25(11) | 1.800(12) | 0.0243(67) | 2.303(58) | 1.41(27) | 0.87(51) | 0.71 |
| linear a=0.5 n=5 (rho_eq=0.97) | 1.759e-06 | 0.102(56) | -0.04(14) | 0.26(12) | 1.814(12) | 0.0218(66) | 2.375(63) | 1.45(30) | 0.83(56) | 0.72 |
| linear a=0.5 n=6 (rho_eq=1.06) | 9.517e-09 | 0.102(58) | -0.05(15) | 0.27(13) | 1.820(12) | 0.0207(66) | 2.407(65) | 1.47(32) | 0.81(58) | 0.72 |
| linear a=0.5 n=8 (rho_eq=1.22) | 1.627e-13 | 0.102(58) | -0.05(15) | 0.27(13) | 1.822(12) | 0.0203(66) | 2.420(66) | 1.48(32) | 0.81(59) | 0.72 |

| linear a=0.2 n=4 (rho_eq=0.55) | 0.06443 | 0.103(39) | 0.039(88) | 0.186(85) | 1.729(12) | 0.0376(68) | 1.997(45) | 1.28(17) | 0.98(37) | 0.73 |
| linear a=0.2 n=8 (rho_eq=0.77) | 0.001315 | 0.101(46) | 0.00(11) | 0.22(10) | 1.772(12) | 0.0294(67) | 2.173(52) | 1.35(23) | 0.94(45) | 0.72 |
| linear a=0.2 n=13 (rho_eq=0.99) | 5.518e-07 | 0.102(49) | -0.02(12) | 0.24(11) | 1.789(12) | 0.0262(67) | 2.251(55) | 1.39(25) | 0.90(49) | 0.71 |
| linear a=0.2 n=20 (rho_eq=1.22) | 2.434e-12 | 0.102(50) | -0.02(12) | 0.24(11) | 1.792(12) | 0.0257(67) | 2.264(56) | 1.40(26) | 0.89(49) | 0.71 |

**Result.**
- **W:** linear-smeared W = 0.10(5)-0.10(6) at every alpha and n, versus flow 0.133(28) at rho=0.75 and 0.142(25) at rho=1. These are statistically compatible, but W does not discriminate here.
- **The linear operator does NOT smooth; it behaves like (or worse than) the raw loop:**
  - eps·s: linear 1.73-1.82, rising with n; raw 1.749(14); flow rho=1 1.413(12).
  - R(s)/R(0): linear 0.020-0.038; raw 0.033; flow 0.114.
  - m_eff(0): linear 2.0-2.42, rising with n; raw 2.08; flow rho=1 1.23.
  - The subtraction-free W estimates disagree with E1 (E3f ≈ 0, E3d ≈ 0.24), as for the raw loop.
- **Cause (checked on a 24^3x32 beta=2.5 config with numpy):** unprojected links lose norm quickly and the loss fluctuates locally.
  - At matched radius rho≈1 the mean link norm is 0.16-0.19, with relative sd 10-15% per link, nearly independent of alpha: 0.152 (a=0.5, n=5), 0.113 (a=0.2, n=13), 0.097 (a=0.05, n=53).
  - A 2x2 loop multiplies 8 such norms, about ±30% local multiplicative noise. That is a UV-local field which dominates the zero-momentum correlator.
  - Smaller alpha helps only marginally.
- **Implication for the Lean anchor switch (PLAN option A):** the linear, positive-coefficient anchor is exactly representable (check (i)), but numerically it has raw-loop spectral content, not the smoothed-operator content seen with the flow (eps·s ≈ 1.8 vs 1.4 at side 2).
  - Rescaling by a constant per step cannot fix this, because ratios are unchanged. Options are a final projection (non-linear) or explicit loop families with designed weights.
  - These are for darthur / YM Bot to weigh. No full linear re-run was launched.
