# S7 — cost estimates (twisted TGF, SU(2)): (A) weak-coupling N_T check, (B) 4th u value

Cost estimates only; nothing launched. MC evidence only, never a proof. Written 2026-10-20 ~11:50 PDT at HEAD b9bb38cd.

## Resources / probes
Pre-check 11:42 PDT: 16 cores (hw.ncpu), 64 GiB, memory free 60%, load 26.9/9.6/5.0 (other users' processes, not ours; untouched).
30 s log `ym_numerics_runs/s7cost/resource_log_s7.log` (11:44:48–11:46:48 PDT, 5 samples): load1 49.8–56.9, free 57–59%, 0 su2gf processes.
load1 > 16 throughout, so by the throttle rule **no timing probe was run (0 MC CPU-h, 100% of the window throttled)**. All timings come from the measured prod5 logs (same binary, flags, eps 0.1, c = 0.3,0.4); analysis-only CPU < 0.01 h.

Measured prod5 cost per "measurement unit" (elapsed / (nmeas + therm/sep), single core, nice 19, 3 procs, load 2–13):
L6 0.0168 s, L8 0.0609 s, L12 0.4375 s, L16 1.973 s, L24 18.09 s (L24: 11396 s for 600 meas, 6290 sweeps = 1.81 s/sweep incl. flow). Timings are β-independent within 0.1%. At the current load (~50) wall times would stretch; the numbers below assume a load like prod5's.

## (A) weak-coupling check of the lattice tree-level N̂_T

Predicted difference (twist_norm.py, plus the literal Ramos numerator P̊²C² − (P̊·C)² with the same momenta/flow kernel):

| c | L | N̂_ours/N_cont − 1 | N̂_Ramos-literal/N_cont − 1 | ours/Ramos − 1 |
|---|---|---|---|---|
| 0.3 | 8 / 12 / 16 / 24 | −0.065 / −0.028 / −0.015 / −0.0068 | −0.472 / −0.456 / −0.452 / −0.449 | +0.77 / +0.79 / +0.80 / +0.80 |
| 0.4 | 8 / 12 / 16 / 24 | −0.036 / −0.016 / −0.0087 / −0.0039 | −0.338 / −0.328 / −0.325 / −0.322 | +0.46 / +0.47 / +0.47 / +0.47 |

The literal printed form does not converge to the continuum N_T. With C_μ → 1, (P̊·C)² → (Σ_μ p_μ)², which is not p². So the two normalisations differ by 45–80%, and the existing β=2000, L=6 check (0.996(13), 1.003(26)) already rules out the literal form at > 15σ. Most likely it is a transcription/convention issue in reading Ramos' formula, not a competing candidate. A check whose only job is to tell the two apart is therefore cheap. The check worth paying for is the sub-percent one that bounds an L-dependent error δ(L) in N̂_T: 1% shifts a pair by about 0.004.

* **A1 (only distinguishes the two forms):** β = 30, 1 chain per L, 200 meas (sep 10, therm 300), L = 8, 12, 16, 24, c = 0.3/0.4 from the same flows. **1.3 CPU-h**, wall ≈ 1.2 h at 3 procs (set by the single L24 chain). Expected precision is about 0.6% (c=0.3) and 1.1% (c=0.4) per L, against a 45–80% difference.
* **A2 (recommended; resolves δ(L) at ≈ 0.25–0.5%):** β = 20 and 40 per L, to separate the O(1/β) term g²/(4/β) − 1 = k/β + δ(L). 1000 meas per (L, β); L24 split into 3 chains of ~334 meas. Per-measurement relative σ is taken from the L=6, β=2000 run: ≈ 0.08 (c=0.3) and ≈ 0.16 (c=0.4), assumed L-independent with τ_int ≈ 1. That gives ≈ 0.25% (c=0.3) and 0.5% (c=0.4) per (L, β). Cost per β: L24 5.17 h, L16 0.56, L12 0.13, L8 0.02, total 5.9 CPU-h. **Total ≈ 11.8 CPU-h; wall ≈ 4.3 h at 3 procs** (6 L24 chains of ~1.9 h in 2 rounds, plus about 1.4 CPU-h of smaller L). Risk: slow low modes at large β could raise τ_int at L=24. A 0.1 CPU-h L=12 probe should confirm the per-measurement σ and τ_int before launch; it was not run here (load > 16).

## (B) 4th u value

**Choice: u ≈ 2.0 (c=0.3), with u ≈ 1.0–1.2 as the alternative.** The current per-u continuum errors scale as σ_s ≈ 0.0038/u (c=0.3: 0.0025, 0.0016, 0.0013 at u = 1.49, 2.40, 2.94), so a low-u point is about 2× noisier at fixed cost. That outweighs its lever-arm gain in the Fisher projection (table). u ≈ 2.0 also fills the 1.5–2.4 gap, keeps β moderate, and gives smaller cutoff/tuning risk. u ≈ 1.0 would test the approach to s0, but it costs more for less.

β (interpolated in 1/g² from prod5, c=0.3, u=2.0): L6 ≈ 3.66, L8 ≈ 3.79, L12 ≈ 3.94; for u=1.0: about 5.6, 5.75, 5.9. Design as prod5: L6 (β6, 2000), L12 (β6, 1200), L8 (β8, 2000), L16 (β8, 1200), L12 (β12, 1200), L24 (β12, 2×600), c = 0.3/0.4 from the same flows.
* β tuning: probes at L = 6, 8, 12, two β each, 150–300 meas (as prod5/probe): **≈ 0.1–0.2 CPU-h**, ≈ 0.1 h wall.
* Production: L24 6.33 + L16 0.67 + L12 0.30 + L8 0.03 + L6 0.01 = **7.35 CPU-h; wall ≈ 3.2 h at 3 procs** (two L24 chains of 3.17 h in parallel, everything else in the third slot).
* **Total B ≈ 7.5 CPU-h, ≈ 3.3–3.5 h wall.** The cost is the same for u ≈ 1.0, because timing is β-independent.

### Projected σ(k1) (GLS, s = s0 + k1 u + k2 u², s0 fixed, k2 free, diagonal errors σ_s ∝ 1/u; reproduces the current 0.0027 / 0.0045)

| 4th u | stats on 4th point | σ(k1) c=0.3 | σ(k1) c=0.4 |
|---|---|---|---|
| none (now) | – | 0.0027 | 0.0045 |
| 1.0 | ×1 (prod5) | 0.0025 | 0.0042 |
| 1.2 | ×1 | 0.0023 | 0.0040 |
| **2.0** | **×1** | **0.0022** | **0.0035** |
| 2.0 | ×4 | 0.0016 | 0.0025 |

A joint common-k1 fit over both c has so far reduced σ by about 0.75× (0.0020 joint vs 0.0027), so u=2.0 at ×1 would give **σ(k1) ≈ 0.0016–0.0017 (joint)**. **σ ≤ 0.0009 is not reachable with a 4th u alone.** k1 and k2 stay ~99% anti-correlated. Reaching 0.0009 would need about 9× the statistics on all 4 u (c=0.3 alone), i.e. roughly 9 × 29 ≈ 260 CPU-h, or a fixed k2 / a better-constrained continuum form. The latter is a modelling assumption, not a statistics gain.
