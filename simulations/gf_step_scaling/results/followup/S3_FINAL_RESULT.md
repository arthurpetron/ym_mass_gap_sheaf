# Items 1–2 FINAL result: two-loop slope k1 of the SU(2) GF step-scaling shift (2026-10-18, analysed 14:43–15:00 PDT)

**Monte Carlo evidence only — not a proof, not a bound.** Scripts: `analysis/stage3_final.py` (stopping rule), `analysis/power_analysis.py` (re-run with actual errors), tables `S3_final.md` / `S3_final.json`, `power_analysis_final.md`, `S3_final_therm.md`.

## Completeness check (jobs3_main.txt = prod3/jobs_main.txt, identical; plus jobs3_probe.txt)
All 31 main + 4 probe jobs complete: every CSV has exactly n_meas rows, indices 0..n-1 unique, last sweep = therm + (n-1)·sep, a single header, constant column count, stderr ends at `meas=N/N` with no errors. No missing or short chain.
Caveat: `run_queue.py` logs `rc=` only for the jobs still running when the launch loop ends (3 of 31: su2_L24_b5.89_u1p0, su2_L16_b5.74_u1p0, su2_L12_b5.89_u1p0b, all rc=0); the other 28 were reaped by `poll()` without logging, so their rc is not recorded. Completion of those is established from the outputs, not from rc.
Thermalisation (first vs second half): |z| <= 2.27 for all 105 (run, observable) values (L=16 beta=3.19: +2.22 for both c; L=8 beta=5.74 probe plaquette +2.27); max|Q| <= 0.008 everywhere (cold starts, Q = 0 sector).
Chain-mean chi2/dof at L=12: beta=3.6: 2.40 / 1.86 (c=0.3/0.4, 4 chains); **beta=3.34 (u~2.9, 12->24): 4.27 / 5.04 (2 chains, 1 dof: the two chains differ by ~2.1–2.2 sigma)**; all others <= 0.78.

## Stopping rule (as specified by darthur): s(u) = 1/u - 1/Sigma = s0 + k1 u + k2 u^2, s0 = 2 b0 ln2 = 0.0644 fixed
Continuum per u = linear fit in (a/L)^2 over 6->12, 8->16, 12->24; u ~ 1.0, 1.54, 1.9, 2.41, 2.9 (scheme's own u); c = 0.3 and 0.4 separately.

| | k1 (c=0.3) | k1 (c=0.4) | classification |
|---|---|---|---|
| **k2 free (primary)** | 0.0016 ± 0.0022 (k2 = -0.0003 ± 0.0009; 0.7σ from 0, 0.5σ from 0.0026) | 0.0089 ± 0.0035 (k2 = -0.0024 ± 0.0013; 2.6σ from 0, 1.8σ from 0.0026) | **UNDECIDED** |
| k2 = 0 | 0.00091 ± 0.00037 (2.5σ from 0, 4.5σ below 0.0026) | 0.00295 ± 0.00059 (5.0σ from 0, 0.6σ from 0.0026) | UNDECIDED (c=0.3 fits neither; c=0.4 alone would be two-loop-consistent) |

Precision requirements (k2 free):
1. σ(k1) <= 0.0009: **FAIL** (0.0022 and 0.0035). (With k2 = 0: pass, 0.00037 / 0.00059.)
2. c=0.3 vs c=0.4 agree within 2σ: Δk1 = +0.0073. **FAIL** with the c-correlation propagated (ρ(k1) = 0.93, same configurations: σ(Δ) = 0.0016, 4.5σ); it would pass only with naive independent errors (σ = 0.0041, 1.8σ). (k2 = 0: Δ = +0.0020, 2.9σ naive / 7.2σ correlated: FAIL.)
3. Extrapolation-form spread (lin vs quadratic in (a/L)^2, with/without 4->8 where it exists — 4->8 exists at every u except u=1.0) below the statistical error: **FAIL** — c=0.3: k1 ranges -0.0038 (lin incl. 4->8) to +0.0059 (quad 3-pair), spread 0.0097 vs σ 0.0022; c=0.4: spread 0.0025 vs σ 0.0035 (pass for c=0.4 only). (k2 = 0: FAIL for both, spreads 0.0084 / 0.0052 vs 0.0004 / 0.0006.) The 4-pair linear fits are rejected (chi2/2 up to 127) and the 3-pair linear fit at u=2.41, c=0.3 has chi2 = 11.7 for 1 dof.

Per-u continuum (lin, 3 finest pairs; one-loop 0.0644; exact two-loop in brackets): c=0.3: u=0.99: 0.0695(53) [0.0670]; 1.54: 0.0649(16) [0.0685]; 1.91: 0.0709(31) [0.0695]; 2.41: 0.0664(12) [0.0710]; 2.88: 0.0665(21) [0.0725]. c=0.4: 1.00: 0.0807(94); 1.58: 0.0700(29); 1.96: 0.0786(52); 2.52: 0.0720(20); 3.05: 0.0691(35).

## PDG sensitivity (L=12 beta=3.6 g2 error × sqrt(chi2/dof of chain means): 1.548 (c=0.3), 1.363 (c=0.4))
k2 free: k1 = 0.0020 ± 0.0022 (c=0.3), 0.0093 ± 0.0035 (c=0.4) -> UNDECIDED; k2 = 0: 0.00098(38), 0.00301(60) -> UNDECIDED. **Classification and all pass/fail outcomes unchanged.** Extra (not in the rule): also scaling L=12 beta=3.34 (factor 2.07 / 2.25): 0.0024(23), 0.0094(36), unchanged.
Additional interpolation systematic (not in the rule): restricting the joint-interpolation beta range for the old-u 6->12, 8->16 pairs moves those shifts by up to 0.0006 (c=0.3) / 0.0014 (c=0.4).

## Power analysis with the ACTUAL errors (`power_analysis_final.md`; statistical only, fixed lin form)
Reproduces σ(k1, k2 free) = 0.00218 / 0.00345. Projections (c=0.3 / c=0.4, k2 free): 2× all statistics 0.0015 / 0.0024 (+50 CPU-h); 4× ("item 4"-like, P2x4) 0.0011 / 0.0017 (+149 CPU-h); 16->32 at u = 1.54, 2.41 ("item 3"-like, P3) 0.0021 / 0.0030 (~40 CPU-h); uniform factor needed for σ <= 0.0009 at both c: 14.7× (~680 CPU-h); CPU-optimal allocation ~250 CPU-h; best achievable within 70 CPU-h: 0.0010 / 0.0015 (still FAIL).
**Recommendation: do not run items 3–4.** Neither, nor both together, reaches σ(k1) <= 0.0009 within the 70 CPU-h cap, and the other two failures (c-scheme disagreement, extrapolation-form spread) are systematic and are not reduced by statistics. (Items 3–4 are read here as the P3 / P2x4 plans of the stopping-rule proposal; they need darthur's approval in any case and were not started.)

## Caveats
MC evidence only, statistical errors, not a proof or bound. The u^2 (three-loop) term of s is scheme dependent, so k2 (and k1 with k2 free) is scheme dependent beyond two loops; large-u comparisons are indicative. Finite-volume/extrapolation: only a/L <= 1/6 (3 pairs) in the primary fit, the linear-in-(a/L)^2 form is not established (form spread above), old-u 6->12 / 8->16 shifts come from a beta-interpolation (M=2), L=12 at beta=3.6 / 4.5 is shared between 6->12 interpolation and 12->24 (correlation neglected), pairs/u treated as independent. Seeds: distinct per chain (prod3: 91001–91004, 92007–92217); all prod3 chains cold-start, i.e. sampled in the Q = 0 sector only (Q != 0 suppressed at these couplings, Stage D; a Q-dependence cannot be measured here).

## Resources (items 1–2 run, Mac darthurtron.local, `resource_guard_stage3.log`)
16 cores (hw.ncpu), 64 GiB RAM (68719476736 B); free RAM min 77% (max 84%); load1 min 2.18 / max 17.62 (one sample > 16); 756 guard samples 07:55:00–14:12:59 PDT, 710 with our processes running (max 3), throttled 1/756 (0.13%), never paused; CPU time ~17.4 CPU-h (sum of per-process elapsed of the 35 single-threaded jobs: L=24 10.3, L=12 4.6, L=16 2.1, L=8 0.3, L=6 0.1; an upper bound since SIGSTOP time would count); wall time 07:55:00 -> 13:52:39 PDT = 5 h 58 min (guard 6 h 18 min). Final analysis: run on the Mac (pre-run 14:43 PDT: 16 cores, 80% memory free, load 5.80/6.67/6.94), < 30 s CPU in total; no new MC launched.
