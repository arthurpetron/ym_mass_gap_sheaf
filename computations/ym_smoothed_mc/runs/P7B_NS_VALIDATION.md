# P7b: polynomial (Newton-Schulz) normalized linear smearing — validation (2026-10-06)

## Code (src/main.rs; binary used: bin/p4run_p7b, built in a separate target dir so the running P7 binary was not touched)
- **Single variant:** `--linear-alpha a --linear-steps n1,.. --linear-ns-k k --linear-global-rescale {avg|<c>}`.
- **Many variants on the same configs:** `--linear-variants "a:k:rescale:n1/n2,..."`.
- **One step:** V = (1-a)U + (a/4) Σ 4 spatial staples. Then optionally one global scalar rescale: divide all spatial links by the lattice-average |V| (`avg`) or by a fixed constant c. Then k Newton-Schulz steps V ← V(3 - |V|^2)/2, where |V|^2 = V^†V is a scalar polynomial for quaternions.
- **Record layout:** the per-linear-level spatial |V| stats (mean, std, min, max after the final step) are appended to each record (header `linnorm:4`; `ana/load.py:load_linnorm`).

## Unit check (`p4run --selftest-ns`, full output runs/p7b/selftest_ns.txt): PASS
- **Scalar map r → r(3-r²)/2:**
  - Converges to 1 quadratically for 0 < r < √3 (r0 = 0.9: 0.9855, 0.99969, 1-1.5e-7) and slowly from the edges (r0 = 0.05 or 1.7: about 1.5× growth per step at first).
  - r0 = 1.75 gives a sign flip toward -1; r0 = 2 → -1 exactly; r0 = 2.5 diverges (−4.06, +27.4, −1e4, ...).
- **Gauge covariance** (4^3x4 hot config, random gauge transform, 3 steps, k = 1, 2, 3, with and without rescale): max |g V g^† − V[U^g]| = 8.9e-16 and max |loops(U) − loops(U^g)| = 2.2e-16.
- **Convergence from near 1:** one step + avg rescale on a hot config gives |V| ∈ [0.56, 1.38]. Max ||V|−1| after k = 1..4 is 0.25, 0.085, 0.011, 1.6e-4.
- The P7 multilinearity self-test still passes (8.8e-17).

## Comparison on identical configs
16^3x32, beta 2.5, side 2, seed 2501 — the same configs as the P7 linear validation, verified: plaquette, flow and plain-linear records bit-identical for the first 500 measurements.
| operator | W E1 | W E3f | W E3d | eps*s | R(2)/R(0) | m_eff(0) | m_eff(1) | |V| mean | |V| std | |V| min | |V| max | corr(O, O_flow rho=1) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| flow rho=0.00 | 0.167(76) | 0.04(14) | 0.19(13) | 1.753(18) | 0.0405(80) | 2.092(72) | 1.11(19) | 1 | 0 | 1 | 1 | 0.6832 |
| flow rho=0.75 | 0.200(42) | 0.156(65) | 0.158(63) | 1.506(17) | 0.0904(94) | 1.399(34) | 1.005(96) | 1 | 0 | 1 | 1 | 0.9641 |
| flow rho=1.00 | 0.205(36) | 0.182(54) | 0.163(49) | 1.400(16) | 0.119(11) | 1.204(27) | 0.928(78) | 1 | 0 | 1 | 1 | 1.0000 |
| linear a=0.5 n=5 NS k=0 rescale=none | 0.120(73) | -0.18(21) | 0.23(17) | 1.804(16) | 0.0250(88) | 2.325(83) | 1.36(35) | 0.1900 | 2.89e-02 | 0.0077 | 0.3572 | 0.5715 |
| linear a=0.5 n=5 NS k=1 rescale=none | 0.200(37) | 0.172(56) | 0.160(51) | 1.413(16) | 0.114(10) | 1.225(27) | 0.944(81) | 0.9997 | 2.04e-03 | 0.2620 | 1.0000 | 0.9991 |
| linear a=0.5 n=5 NS k=2 rescale=none | 0.203(36) | 0.177(55) | 0.162(50) | 1.403(16) | 0.118(11) | 1.210(27) | 0.930(79) | 1.0000 | 5.15e-05 | 0.6636 | 1.0000 | 0.9997 |
| linear a=0.5 n=5 NS k=3 rescale=none | 0.203(36) | 0.178(55) | 0.161(50) | 1.404(16) | 0.118(11) | 1.210(27) | 0.930(79) | 1.0000 | 8.06e-07 | 0.9732 | 1.0000 | 0.9997 |
| linear a=0.5 n=5 NS k=1 rescale=avg | 0.201(36) | 0.175(55) | 0.160(50) | 1.406(16) | 0.116(11) | 1.214(27) | 0.936(80) | 0.9999 | 1.10e-03 | 0.3485 | 1.0000 | 0.9997 |
| linear a=0.5 n=5 NS k=2 rescale=avg | 0.203(36) | 0.178(55) | 0.161(50) | 1.404(16) | 0.118(11) | 1.210(27) | 0.930(79) | 1.0000 | 4.37e-05 | 0.5634 | 1.0000 | 0.9997 |
| linear a=0.5 n=5 NS k=3 rescale=avg | 0.203(36) | 0.178(55) | 0.161(50) | 1.404(16) | 0.118(11) | 1.210(27) | 0.930(79) | 1.0000 | 6.89e-07 | 0.9760 | 1.0000 | 0.9997 |
| linear a=0.2 n=13 NS k=0 rescale=none | 0.132(65) | -0.15(18) | 0.21(15) | 1.782(16) | 0.0288(90) | 2.214(73) | 1.33(31) | 0.1686 | 1.91e-02 | 0.0184 | 0.2676 | 0.6102 |
| linear a=0.2 n=13 NS k=1 rescale=none | 0.206(36) | 0.182(54) | 0.166(49) | 1.398(16) | 0.119(11) | 1.200(27) | 0.925(78) | 1.0000 | 9.91e-05 | 0.8769 | 1.0000 | 0.9999 |
| linear a=0.2 n=13 NS k=2 rescale=none | 0.206(36) | 0.183(54) | 0.165(49) | 1.398(16) | 0.119(11) | 1.200(27) | 0.925(78) | 1.0000 | 2.31e-07 | 0.9965 | 1.0000 | 1.0000 |
| linear a=0.2 n=13 NS k=3 rescale=none | 0.206(36) | 0.183(54) | 0.165(49) | 1.398(16) | 0.119(11) | 1.200(27) | 0.925(78) | 1.0000 | 8.67e-10 | 1.0000 | 1.0000 | 1.0000 |
| linear a=0.2 n=13 NS k=1 rescale=avg | 0.206(36) | 0.182(54) | 0.166(49) | 1.397(16) | 0.119(11) | 1.200(27) | 0.925(78) | 1.0000 | 8.59e-05 | 0.8845 | 1.0000 | 0.9999 |
| linear a=0.2 n=13 NS k=2 rescale=avg | 0.206(36) | 0.183(54) | 0.165(49) | 1.398(16) | 0.119(11) | 1.200(27) | 0.925(78) | 1.0000 | 1.30e-07 | 0.9966 | 1.0000 | 1.0000 |
| linear a=0.2 n=13 NS k=3 rescale=avg | 0.206(36) | 0.183(54) | 0.165(49) | 1.398(16) | 0.119(11) | 1.200(27) | 0.925(78) | 1.0000 | 1.58e-09 | 1.0000 | 1.0000 | 1.0000 |

## Verdict
- **k = 1 already recovers flow-like smoothing; k = 2-3 matches the rho = 1 flow operator essentially exactly.**
  - alpha = 0.5, n = 5, k ≥ 2: W 0.203(36), eps·s 1.404(16), R(2)/R(0) 0.118(11), m_eff(0) 1.210(27). Flow rho = 1 gives 0.205(36), 1.400(16), 0.119(11), 1.204(27).
  - alpha = 0.2, n = 13, k ≥ 1 agrees with flow within 0.002 in eps·s.
  - Per-config correlation with the flow operator is 0.9997-1.0000.
  - Plain linear (k = 0) remains raw-like: eps·s 1.80/1.78, R(2)/R(0) 0.025/0.029, m_eff(0) 2.33/2.21, corr 0.57/0.61.
- **The global rescale is unnecessary here.** It only speeds NS slightly at k = 1 (eps·s 1.406 vs 1.413 at alpha = 0.5) and has no effect at k ≥ 2.
- **NS never diverged in any variant.** Before NS, every linear step of normalized-ish links gives |V| ≤ 1 (a convex combination of near-unit quaternions). With the avg rescale, max |V| ≤ 1/mean ≈ 1.2 < √3.
  - The risk is at the low end: the per-step minimum |V| can approach 0 (plain linear min 0.008), and there NS converges slowly (factor 1.5 per step). That is the origin of min |V| = 0.26 at alpha = 0.5, k = 1, and 0.66 at k = 2.
  - Divergence (|V| ≥ √3) would need an over-scaled fixed constant c, or NS applied once at the end after many unnormalized steps. Plain linear ends with mean |V| 0.17-0.19, but a fixed rescale would have to map its spread 0.008-0.36 inside (0, √3), and 0.008 is hopeless.
  - **So per-step NS is required; end-only NS is not viable.**
- **Implication:** linear staple smearing + k = 2 Newton-Schulz per step is a polynomial, gauge-covariant map that reproduces the flow-smoothed spectral content at matched radius. Coefficients are no longer all positive, as noted in the task.
