# P6 — window-survival estimator audit, tau_int, raw vs smoothed, scopes (2026-10-06, box)

Analysis only (no new MC). Data: P5 rho-scan runs b2.50 s2, b2.60 s3, b2.70 s4, b2.85 s6 (24^3x32, 500-600 meas), b2.95 s8 (32^3x48, 240), b3.00 s10 streams A+B (32^3x48, 2x170). Stream C (seed 3003) untouched, still running (meas 10/170 at 05:51 PT, ~41 s/meas, so ETA about 07:45 PT).
Detailed tables: P6_WINDOW_ESTIMATORS.md (all rho, all estimators, Fejer box), P6_TAU.md, P6_RAW_VS_SMOOTH.md. Raw JSON: p6/*.json. Scripts: ana/p6_window.py, p6_tables.py, p6_raw.py, p6_poly*.py.

## (a) W = R(s+1)/R(s//2) per estimator (jackknife, bins never straddle streams)
E1 = per-stream global subtraction; E1c = E1 + bias correction Var(<O>_stream) from bin scatter; E2 = per-block (jackknife-bin) subtraction; E3f = subtraction-free far-lag Q(n)-Q(Lt/2); E3d = subtraction-free differenced D(n)=Q(n)-Q(n+1), W_D = D(s+1)/D(s//2) (not identical to W unless one state dominates both lags).

rho = 1.00
| beta | s | W E1 | W E1c | W E2 | W E3f | W E3d | c0 (E1) | -2logW | R(s)/R(0) | eps*s E1 / E2 / E3f | eps_shift*s |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 2.50 | 2 | 0.203(28) | 0.204(28) | 0.142(29) | 0.146(45) | 0.132(37) | 7.8(14) | 3.19(28) | 0.114(9) | 1.402(16) / 1.432(16) / 1.430(21) | 0.94(13) |
| 2.60 | 3 | 0.127(24) | 0.128(24) | 0.079(23) | 0.144(43) | 0.107(32) | 13.7(29) | 4.12(37) | 0.095(10) | 1.788(22) / 1.827(22) / 1.774(34) | 1.37(22) |
| 2.70 | 4 | 0.224(44) | 0.226(44) | 0.109(38) | 0.170(57) | 0.155(58) | 6.9(17) | 3.00(39) | 0.100(10) | 2.076(29) / 2.150(30) / 2.112(40) | 1.61(32) |
| 2.85 | 6 | 0.242(36) | 0.244(36) | 0.120(39) | 0.305(48) | 0.186(59) | 6.3(12) | 2.84(30) | 0.091(11) | 2.369(45) / 2.457(47) / 2.314(66) | 1.86(29) |
| 2.95 | 8 | 0.355(58) | 0.359(58) | 0.232(65) | 0.354(85) | 0.339(98) | 3.6(9) | 2.07(33) | 0.127(21) | 2.363(92) / 2.484(97) / 2.36(15) | 1.15(50) |
| 3.00 | 10 (A+B) | 0.25(14) | 0.27(14) | -0.30(15) | -0.10(27) | 0.128(61) | 6.0(46) | 2.8(11) | 0.089(48) | 2.064(91) / 2.371(75) / 2.285(97) | 1.4(10) |
| 3.00 | 10, first 60/stream dropped | 0.005(194) | 0.03(19) | -0.44(20) | -0.44(48) | 0.151(79) | – | – | – | 2.21(10) | – |

rho = 0.75
| beta | s | W E1 | W E1c | W E2 | W E3f | W E3d | c0 (E1) | -2logW | R(s)/R(0) | eps*s E1 / E2 / E3f | eps_shift*s |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 2.50 | 2 | 0.197(34) | 0.198(34) | 0.137(35) | 0.159(50) | 0.120(46) | 8.1(17) | 3.25(34) | 0.086(8) | 1.505(15) / 1.531(15) / 1.521(21) | 0.86(18) |
| 2.60 | 3 | 0.095(25) | 0.095(25) | 0.047(24) | 0.114(44) | 0.062(40) | 19.1(55) | 4.71(52) | 0.068(9) | 1.983(21) / 2.017(20) / 1.968(34) | 1.59(29) |
| 2.70 | 4 | 0.149(48) | 0.151(48) | 0.038(43) | 0.134(64) | 0.054(77) | 11.4(43) | 3.81(64) | 0.064(8) | 2.376(33) / 2.433(34) / 2.384(44) | 2.13(48) |
| 2.85 | 6 | 0.195(46) | 0.197(45) | 0.102(53) | 0.269(68) | 0.200(88) | 8.3(24) | 3.27(47) | 0.051(9) | 2.799(38) / 2.854(39) / 2.747(58) | 1.73(55) |
| 2.95 | 8 | 0.351(69) | 0.355(69) | 0.254(76) | 0.31(10) | 0.30(11) | 3.7(11) | 2.09(39) | 0.092(18) | 2.900(78) / 2.990(79) / 2.94(13) | 0.90(74) |
| 3.00 | 10 (A+B) | 0.25(14) | 0.27(14) | -0.23(15) | -0.05(24) | 0.080(71) | 6.0(45) | 2.8(11) | 0.066(37) | 2.68(10) / 2.952(76) / 2.87(10) | 0.93(87) |
| 3.00 | 10, first 60/stream dropped | 0.046(190) | 0.07(19) | -0.34(20) | -0.31(40) | 0.106(98) | – | – | – | 2.860(92) | – |

Other rho (0, 0.5, 1.25, 1.5) and a single-exponential-plus-constant fit (E3o) are in P6_WINDOW_ESTIMATORS.md. At rho=0 the raw s x s loop correlator is drowned before lag s+1 for every s >= 3, so raw W is undefined there.
Fejer time-box (Lean timeKernel, weights 1/(M+1), lags 0..M; R_Y(n) = (M+1)^-2 sum_{k,l<=M} R(n+k+l)), rho=1: s2: M=1 0.259(40), M=2 0.289(55); s3: 0.127(42), 0.087(64); s4: 0.238(69), 0.237(96), M=4 0.28(16); s6: 0.255(48), 0.253(66), M=3 0.221(95); s8: 0.349(72), 0.314(87), M=4 0.24(12); s10: 0.29(17), 0.35(18), M=5 0.61(15) (s10 M=5 reaches lag 21 of 24, noise/offset-dominated). The box smoothing does not change W significantly where it is readable (M <= 2).

## (b) tau_int of the operator mean (binning)
Smoothed operator means (rho >= 0.5) are NOT plateaued at ANY side: tau(b) rises out to the largest available bin, e.g. at rho=1 tau(16) = 1.20 (s2), 1.41 (s3), 1.88 (s4), 1.72 (s6); tau(8) = 1.82 (s8), 2.64 (s10). It grows with rho and with beta. Raw (rho=0) means are fine (tau ~0.5). The jackknife ERROR of W (E1) vs bin size does plateau for s <= 6, but is still RISING for s = 8 (0.044 at b=1 to 0.073 at b=16) and s = 10 (0.042 to 0.095 at b=8; stream B 0.083 to 0.211). Flags: s8 and s10 have a slow-mode problem in W itself. s<=6 errors are OK, but the operator mean has a slow component.
s10 is worse than slow. It is not thermalized in the smoothed long-distance operator. Stream B's <O>(rho=1) drifts monotonically by quintile (0.844, 0.841, 0.854, 0.863, 0.871); stream A also drifts (0.865 to 0.884). The plaquette is flat. The stream means differ by 5.0 sigma (naive). In pooled subtraction the stream-offset term (dM/2)^2 is 0.11 R(0), larger than R(11) itself (0.09 R(0)). The s=10 W moves from 0.25 to 0.00 to -0.09 (E1) as the first 0/60/85 meas per stream are dropped. **Conclusion: the s=10 W is currently undetermined. Only the differenced estimator E3d is stable, at 0.13-0.15(6-9).**

## (c) Sensitivity of W to the subtraction choice
Correlated (jackknifed-difference) pulls relative to E1:
- **E2 (per-block):** sits 4-7.5 sigma BELOW E1 at every side. Typical shifts are -0.05 (s2, s3), -0.11 (s4), -0.12 (s6, s8), -0.55 (s10). This is the expected constant-offset bias -Var(bin mean). It measures how much a vacuum offset of block size would move W. Because tau is not plateaued, E1 is biased low by somewhere between Var(global mean) (the E1c correction: +0.001 to +0.004 for s<=8, +0.024 at s10) and the E2 shift.
- **Subtraction-free E3f and E3d:** agree with E1 within 2.2 sigma for s <= 8 (E3f 0.0-1.7 sigma, E3d 0.1-2.2 sigma), though with 1.5-3x larger errors.
- **Spread** (max-min over E1, E1c, E2, E3f, E3d) in units of sigma_E1 at rho=1: 2.5 (s2), 2.8 (s3), 2.7 (s4), 5.1 (s6), 2.2 (s8), 4.1 (s10). At rho=0.75: 2.3, 2.7, 2.4, 3.7, 1.5, 3.6.
- **Robust W (rho=1), range over E1 and the subtraction-free E3f/E3d:** about 0.13-0.20 (s2), 0.11-0.14 (s3), 0.16-0.22 (s4), 0.19-0.31 (s6), 0.34-0.36 (s8). s10 is undetermined.

## (d) Raw vs smoothed
- **Raw s x s loops drown almost immediately.** The drowning lag is 3-4 at beta 2.50-2.60, 2 at 2.70, 2 at 2.85 (5x5: 3-4), and 1 at 2.95 and 3.00 (no readable raw m_eff at all). Smoothed (rho 1-1.5) operators stay readable to lag 6-13.
- **Where both are readable (beta <= 2.60, n <= 2):** raw m_eff >= smoothed m_eff at every lag, e.g. b2.50 n=1: raw 2x2 1.22(19), raw 1x1 1.31(30), smoothed rho=1 0.96(7). At n=2 they are compatible: raw 0.83(46) vs 0.63(12). b2.60 n=1: raw 3x3 1.17(28) vs 0.81(4). P4 runs (independent configs) agree. The pattern is the normal excited-state contamination, with no raw m_eff falling below smoothed. But the raw window is too short for this to be a strong test beyond beta 2.60.
- **rho dependence:** at fixed lag m_eff decreases monotonically with rho and the curves converge from above (b2.85 n=5: 0.45, 0.34, 0.30, 0.27 for rho 0.75-1.5; b2.95 n=5-8: about 0.22 for rho >= 0.75). That is consistent with a common asymptotic rate, and no rho-dependent asymptote is resolved.
- **Two warnings:**
  1. At s10 the m_eff for rho >= 1 RISES with lag (0.18 to 0.26). This signals a negative constant offset in C (the subtraction/thermalization issue above), not physics.
  2. Finite volume. With the extrapolated scale, L*sqrt(sigma) = 1.52 (b2.85 L24), 1.50 (b2.95 L32) and 1.30 (b3.00 L32). The last is below the SU(2) critical size 1/(Tc/sqrt sigma) ~ 1.41. The leading-order two-torelon energy, 2 a m_T = 2(sigma a^2 L - pi/3L), is 0.10, 0.075 and 0.04 there, well below a m0++ = 0.24, 0.18, 0.15. So **a light state with weak overlap on the contractible smoothed loop (torelon pairs / center-sector tunnelling) is expected at s6 (L24), s8 and s10** and could cause both the slow mode and the s10 stream offset.
  - None of the smoothed m_eff go below a m0++ within the readable lags (b2.95 plateau about 0.22, b3.00 0.16-0.18), so it is not seen directly.
  - The APE-smeared spatial Polyakov loops on the final configs are suggestive but not conclusive: |<P_spatial>| up to 0.52 at b2.85 L24 and b3.00 A, versus 0.05-0.19 at b2.70 L24. But single-configuration temporal loops also reach about 0.19-0.36.
  - Recommend logging the smeared spatial Polyakov loop per measurement in any rerun.
- **Scale caveat:** this is t0 extrapolated beyond the Hirakida fit range for beta >= 2.95.

## (e) SCOPE (not launched): larger-Ls rerun at beta 2.95, side 8
Reference: 32^3x48 at 3 threads uses about 650 MB RSS and 32.8 s/meas (interval 4 + 4 OR + spatial flow to t=24 at the 5 levels plus loops; the flow dominates). Cost scales with Ls^3. Keep Lt=48 (lags <= 9 << 24).
| Ls | L sqrt(sigma) | 2 a m_T (LO) vs a m0++=0.177 | RAM | s/meas 3 thr | 240 meas 3 thr | 6 thr (after C ends, ~1.7x) |
|---|---|---|---|---|---|---|
| 32 (now) | 1.50 | 0.075 | 0.65 GB | 33 | 2.2 h | 1.3 h |
| 40 | 1.87 | 0.123 | 1.3 GB | 64 | 4.3 h | 2.5 h |
| 48 | 2.25 | 0.167 | 2.2 GB | 111 | 7.4 h | 4.4 h |
| 56 | 2.62 | 0.209 | 3.5 GB | 176 | 11.7 h | 6.9 h |
Thermalization: 300 sweeps is not enough for the smoothed observables. Use at least 1000 heatbath+OR sweeps (about 8 min at Ls=32, scaling as Ls^3), then discard measurements until the <O(rho=1)> running mean is flat. Add a spatial Polyakov-loop (smeared) record per measurement for the torelon check.
**Recommendation:** Ls=48 (two-torelon threshold about at m0++) with 2 independent streams × 120 meas on 3 threads each, once stream C finishes: about 3.7 h wall, 4.4 GB total RAM (fits in the about 5 GB free; or run 1 stream × 240 meas at 6 threads, 4.4 h, 2.2 GB). Ls=40 is the cheap intermediate (2.5 h at 6 threads), but it is still below threshold.

## (f) SCOPE (not implemented): linear unprojected spatial staple smearing (PLAN option A)
Code change in src/main.rs (about 40 lines):
1. **New function** `linear_smear_step(src, dst, g, alpha, nth)`. It uses the same checkerboard-free, timeslice-parallel loop as `flow_step`. For spatial mu: `dst[s,mu] = (1-alpha)*src[s,mu] + (alpha/4)*S_mu(s)`, where S_mu = `staple(src, g, s, mu, SPA\{mu})`. That is the 4 spatial staples, in the same orientation as U_mu(x); apply `dag()` if `staple()` returns the closing-path orientation (check against `flow_step`'s `mul(a, dag(u))`). Temporal links are copied. There is NO `exp`, NO `renorm`: links stay as unnormalized quaternions, i.e. elements of R^4 = R_+ · SU(2) ∪ {0}.
2. **Flags** `--linear-alpha a` and `--linear-steps n1,n2,...` (cumulative step counts per level, replacing `--tflow` when given). `loops()` needs no change: it only uses `mul` and the scalar part, which are multilinear, so the measured loop is exactly a positive linear combination Σ c_w W_w of unsmeared Wilson loops (the Lean ψ form). Normalization cancels in W, eps and m_eff. E_s should be reported unnormalized and normalized by the product of link norms.
3. **Matching:** n ≈ 4 t/alpha = (2/3)(rho s)^2/alpha (linearized flow, stout-equivalence n·alpha/4 ≈ t). With alpha=0.5, rho=1: n = 5 (s2), 12 (s3), 21 (s4), 48 (s6), 85 (s8), 133 (s10). Check the matching once by comparing E_s and the m_eff(n=0) of linear vs Wilson flow at equal radius on a 16^3x32 test.
4. **Cost:** a linear step ≈ 0.8 of a flow step (no exp/renorm). Configs were not saved, so re-measuring W means regenerating them. Running both smearings per config (to compare on identical configs) adds about 50-80% per measurement. Estimate for all sides at rho {0.75, 1.0} plus Wilson flow on the same configs, at 3 threads:
   - s2-s6 on 24^3x32 at the P5 statistics: 500-600 meas × (2.3-6.5 s) × 1.6, about 0.5-1.7 h each, about 4 h total;
   - s8 at 32^3x48 × 240 meas: about 3.5 h;
   - s10 needs the thermalization/volume fix first.
   - About 5 h total for s<=6 plus s8 at 6 threads once C is done. A 16^3x32 validation is about 10 min.
   Optional `--save-configs every k` (201 MB per 32^3x48 config) would make future smearing variants analysis-only.

## Heat-kernel action feasibility (plan only, YM Bot item b)
- **Target:** the plaquette weight K_w(U) = Σ_j (2j+1) w^{c·j(j+1)} χ_j(U), with the repo's nome w and g^2 = -4 log w (2026-10-06: that is the heat-kernel time t, a repo label; the standard Wilson-normalized coupling is g^2 = 2t = -8 log w, i.e. beta = 4/g^2 = -1/(2 log w) at leading order). The constant c and the j(j+1) vs (n^2-1)/4 convention must be read from the repo's carrier definition (not available on the box; the repo is not here).
- **Heatbath:** single-link update with staple sum A = Σ_p (other 3 links). The local density is Π_p K_w(U X_p) over 6 plaquettes and is no longer exp(β Re tr UA)-factorizable. Two options:
  1. Metropolis on top of KP heatbath with an effective beta_eff(w) matched by the 1st character coefficient, accepting with the ratio Π K_w / exp(beta_eff Re tr).
  2. Precompute K_w on a grid of the class angle θ (truncate Σ_j at j_max where w^{j(j+1)} < 1e-16; j_max ≤ 30 for g^2 ≥ 0.5) and do a Metropolis/heatbath in θ with tabulated log K.
  - Option 1 costs about 1.5-2x per sweep (6 extra plaquette traces + table lookup) and keeps the existing checkerboard code. Acceptance is about 70-90% for beta near 2.5-3.
- **Validation:** strong/weak-coupling plaquette vs the exact character-expansion values on 4^4 and 8^4. Scale setting by t0 at 2-3 nomes, matching to Wilson via the known beta_HK ↔ beta_W relation.
- **Estimate:** about 1 day of coding/validation and about 2-3 h of compute for a 2-nome check. Not started.

## Resources (P6)
All P6 compute was single-threaded Python (1 core) next to stream C (3 threads).
- Start 05:34 PT: 15 GB total, MemAvailable about 5.6 GB, load 3.11.
- During: MemAvailable 5161-5609 MB (32-35%), load1 3.1-4.1.
- End 05:51 PT: MemAvailable 5255 MB, load 3.13.
- No throttle conditions (free RAM never below 15%, load1 never above 8). The 30 s sampler was not used for this short analysis; spot readings are in p6/resources_snapshot.txt.
