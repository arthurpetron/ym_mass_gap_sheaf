# S9 — cost estimates, twisted box: pairs 8→16, 12→24, 16→32 (6→12 dropped); u widened to ~4.5

COST ONLY: no MC was run. Written 2026-10-20 ~23:50 PDT on top of 55d605ec (prod6 final). MC evidence only, never a proof.

## Resources
At 23:46 PDT the machine had 16 cores, 64 GiB, load 53.6/46.2/34.0 and 61% memory free, all from other users. load1 > 16, so **no probes were run (0 MC CPU-h)**. Analysis < 0.01 CPU-h.

## Timing basis (measured, prod5/prod6, 1 core, nice 19; cost per "unit" = elapsed/(nmeas + therm/sep), β-independent)
L8 0.0609 s, L12 0.4375 s, L16 1.973 s, L24 18.09 s (prod6 L24: 11441–11560 s / 630 units).
**L32: not measured** (load). (32/24)^5 × L24 gives 76 s/unit. The measured L16→L24 scaling (exponent 5.47) gives 87 s/unit. Totals use 76, and the ^5.5 figure is in brackets.
L32 memory: 32⁴ × 4 links × 32 B = 134 MB per gauge field. Including flow copies and clover fields, about 0.5–1 GB RSS per process, so 3 processes need < 3 GB of 64 GiB (not measured).

## Proposed u values and β (c = 0.3 defines u; c = 0.4 from the same configs)
Existing: 1.49, 2.01, 2.40, 2.94. **New: u ≈ 3.6 and u ≈ 4.5.** u ≈ 5.0 is optional (see risks).
β is interpolated or extrapolated linearly in 1/g² vs β from prod5/6 (local slope ≈ 0.27 per unit β). Uncertainty is about ±0.03 for u ≤ 3.6 and ±0.05–0.08 at u = 4.5–5, because 1/g² bends at strong coupling, so it **must be tuned**.

| u | β8 (8→16) | β12 (12→24) | β16 (16→32) | status |
|---|---|---|---|---|
| 1.49 | 4.44 | 4.60 | ≈4.70 | β8, β12 exist; β16 new |
| 2.01 | 3.785 | 3.929 | ≈4.04 | β8, β12 exist; β16 new |
| 2.40 | 3.47 | 3.62 | ≈3.735 | β8, β12 exist; β16 new |
| 2.94 | 3.21 | 3.33 | ≈3.44 | β8, β12 exist; β16 new |
| 3.6 | ≈2.95 | ≈3.10 (L12 at 3.08 gives 3.69) | ≈3.21 (L16 at 3.21 gives 3.61) | all new |
| 4.5 | ≈2.75 | ≈2.90 | ≈3.01 | all new |
| (5.0) | ≈2.67 | ≈2.82 | ≈2.92 | optional |

**Risks at u ≳ 4 on L = 8.**
* **Strong coupling.** β8 ≈ 2.75 (u = 4.5) and 2.67 (u = 5) are within ~0.4–0.5 of the SU(2) Wilson-action strong/weak crossover (β ≈ 2.2–2.3; no true bulk transition for SU(2)). Cutoff effects in 8→16 will be large, and the quadratic s(u) model may need a u³ term (table below).
* **Topology.** prod5/6 never left Q = 0 (max |Q| ≤ 0.03 at L6, β 3.08). At β ≈ 2.7–3.0 dislocations and small instantons become common, so tunnelling into Q ≠ 0 at L = 8 (and possibly L = 12) is plausible. With n12 = 1 only, Q is integer here, and the twisted-box Q ≠ 0 weight is unmeasured. At L = 24/32 local updates freeze Q instead, so the L and 2L ensembles of a pair can sample different sector mixtures.
* **Mitigation.** Log Q per configuration, analyse sector by sector, and report the Q ≠ 0 fraction. Treat u = 5 at L = 8 as high risk; I don't recommend it.

## Statistics (matched to prod5/6) and CPU-h per item
L8 2000 meas (1 chain), L12 1200, L16 1200, L24 2 × 600, L32 4 × 300 (therm 300 sweeps per chain = 30 units).
Per-ensemble CPU-h: L8 0.034, L12 0.15, L16 0.674, L24 6.33, **L32 27.9 [31.9]**.

| item | content | CPU-h |
|---|---|---|
| 16→32 at the 4 existing u | L16(β16) + L32(β16) each = 28.6 [32.6] | 114.4 [130.3] |
| u = 3.6, 4.5 (all 3 pairs) | L8 + L16(β8) + L12 + L24 + L16(β16) + L32 = 35.8 [39.8] each | 71.5 [79.5] |
| β tuning | L8, L12, L16 at 2 β for the 2 new u, plus L16 at 1–2 β for the 4 existing u (300 meas) | ≈ 1.7 |
| **FULL total** | | **≈ 188 [≈ 211] CPU-h** |

**Wall time at 3 procs:** 24 L32 chains of 7.0 [8.0] h dominate. That is about 63 [71] h with ideal packing and load ≤ 16. At the current load (> 16) the guard holds us to 1 process, so expect **≈ 190–210 h**.
The full plan is over 60 CPU-h, so here are reduced options:
* **R1 (recommended): add u = 3.6 and 4.5 with pairs 8→16 and 12→24 only (no 16→32).** 2 × 7.19 + tuning ≈ 0.3 gives **≈ 14.7 CPU-h, ≈ 6.5 h wall at 3 procs** (4 L24 chains of 3.2 h in 2 rounds).
* **R2: R1 plus 16→32 at u = 2.9 and 4.5 only**, L32 with 2 × 300 meas (13.9 h each) plus L16(β16). That is 2 × 14.6 + R1 ≈ **44 CPU-h, ≈ 15–17 h wall**. It gives a third, finer pair at one low and one high u as a cutoff check. Precision is lower, because the L32 statistics are half matched.

## Projected σ(k1), k2 free (Fisher/GLS, s = s0 + k1 u + k2 u², s0 = 0.0644 fixed, c = 0.3, diagonal errors)
Model: continuum σ_s(u) ≈ 0.0037/u (current T1.636 c=0.3: 0.0024, 0.0019, 0.0016, 0.0013), scaled by the ratio of the (a/L)² extrapolation errors for the new pair set. That ratio is 0.98: 16→32 at matched statistics barely changes the statistical error, because it trades 6→12's leverage for smaller cutoff effects. The model reproduces the current σ(k1) = 0.0021.

| design | σ(k1) c=0.3 | corr(k1,k2) | with free u³ term |
|---|---|---|---|
| now (4 u, 6→12/8→16/12→24) | 0.0021 | −0.988 | – |
| 4 u, 8→16/12→24/16→32 | 0.0021 | −0.988 | 0.010 |
| **+ u 3.6, 4.5 (full or R1)** | **0.00075** (R1: 0.00076) | **−0.983** | 0.0029 |
| + u 3.6, 4.5, 5.0 | 0.00060 | −0.986 | 0.0022 |
| + u 4.5 only | 0.00081 | −0.981 | 0.0040 |

c=0.4 errors are about 1.7× larger, giving about 0.0013 with u = 3.6 and 4.5. A common-k1 joint fit over both c (×0.78 so far) gives about **0.0006–0.0010**.

**Plain verdict.**
* Widening u to 4.5 brings the c=0.3 σ(k1) to ≈ 0.0008, **just under 0.0009 if the u² model holds**. c=0.4 alone stays ≈ 0.0013, so Precision 1 for both c is not reached; only the joint fit gets near 0.0009.
* The k1–k2 anticorrelation is **not broken**: it stays at ≈ −0.98, which is intrinsic to a fit in u and u² with s0 fixed. A wider range lowers σ(k1) only through leverage.
* If a u³ term is needed at u ~ 4.5, which is plausible given the strong coupling at L = 8, σ(k1) goes back to ≈ 0.003.
* The original rule also requires a form spread below σ (Precision 3). Currently c=0.4 fails at 0.013. That is unlikely to pass at σ ≈ 0.0008, because the a⁴/quad forms will spread more at u = 4.5.
* So: **σ ≤ 0.0009 is reachable only for c=0.3 / the joint fit, and only under the quadratic model. The full original rule does not look reachable** with this plan.
* 16→32 buys cutoff control (systematics), not k1 precision. R1 gets essentially the same σ(k1) for ≈ 15 CPU-h instead of ≈ 190.
