# S8: prod6 results summary: (A2) weak-coupling check of the twisted N̂_T, (B) 4th u ≈ 2.0 and the 4-u twisted step-scaling fit

**Monte Carlo evidence only. This is not a proof and not a bound.** Errors are statistical only: a moving-block bootstrap (blocks of 10 configurations, the same indices for c = 0.3 and 0.4), cross-checked with the Γ method and a binned jackknife. Written 2026-10-20, about 21:10 PDT, on top of 77ade78b.
Production: `ym_numerics_runs/prod6` on the Mac. 19 jobs (`prod6/jobs6_prod.txt`); queue 13:43:05 → 20:05:22 PDT, guard until 20:25:47 PDT. Pre-runs and the plan are in `prod6/` (PROD6_PLAN.md, prepro.txt).
Detailed outputs: `S8_tw6_checks.md` (completeness, thermalisation, topology, resources), `S8_a2_analysis.md` (A2), `S8_tw4_analysis.md` (B, primary), and the B sensitivity variants
`S8_tw4_analysis_{3u_check,excl_twe,excl_twd,B20,normcont}.md`. Scripts: `analysis/tw6_checks.py`, `analysis/a2_analysis.py`, `analysis/tw4_analysis.py` (tw_analysis.py generalised to the prod5 + prod6 directories and 4 u).

## Completeness
I verified all 19 jobs from the outputs. Each .csv has exactly n_meas rows with unique indices 0..n−1 and no duplicates. Each has one header pair with twist=n12 and the job's seed, 9 columns, last sweep = therm + (n−1)·sep, a matching .plaq length, and a stderr that ends at meas=N/N. queue.log logged `finished … rc=0` for only 3 jobs (L12 β20, L8 β20, L6 β3.658), because run_queue.py only logs the jobs still running when its launch loop ends. The other 16 rest on the output checks above.

## A2: weak-coupling check of the lattice tree-level N̂_T(c, L)
R = g²_TGF/g0², g0² = 4/β, β = 20 and 40, L = 8, 12, 16, 24. L=24 pools 3 independent chains (wca/wcb/wcc) per β.
δ_meas(L) = 2R40 − R20 − 1 = δ_tree(L) − 0.02·b(L) + O(g0⁶), where R − 1 = δ_tree + a g0² + b g0⁴. With only two β, the O(g0⁴) term b is not separable.

| L | δ c=0.3 | δ c=0.4 | δ(0.4)−δ(0.3) (corr.) | δ if the continuum N_T were used (c=0.3) |
|---|---|---|---|---|
| 8 | −0.0114(32) (−3.6σ) | −0.0122(59) (−2.1σ) | −0.0008(33) | −0.0757(30) |
| 12 | −0.0011(40) | +0.0020(76) | +0.0031(42) | −0.0288(39) |
| 16 | −0.0075(43) (−1.7σ) | −0.0123(86) (−1.4σ) | −0.0048(50) | −0.0227(42) |
| 24 | +0.0047(51) [Birge-inflated (71)] | +0.0099(99) [(114)] | +0.0052(56) | −0.0021(51) |

* Fits over L (independent ensembles). At c=0.3: δ ≡ 0 gives χ² = 16.7/4 (p = 0.002); a constant gives −0.0056(20) with χ² = 8.9/3 (p = 0.03); d0 + d2/L² gives d0 = +0.0019(37), d2 = −0.84(36) (−2.4σ) with χ² = 3.2/2. At c=0.4: δ ≡ 0 gives χ² = 7.4/4 (p = 0.12); d2 = −1.00(68) (−1.5σ). Inflating the L=24 errors for the chain scatter (Birge) gives d2 = −0.75(38) (−2.0σ) at c=0.3.
* L ≥ 12 alone, c=0.3: −0.0011(40), −0.0075(43), +0.0047(51), so χ²(δ≡0) ≈ 4.0/3. That is consistent with no normalisation error at the 0.4–0.5% per-L level.
* **Answer to "does our twisted N_T normalisation have an L-dependent error?"** The lattice N̂_T is strongly preferred over the continuum N_T: the continuum alternative is off by −20σ at L=8 and −7σ at L=12 (c=0.3). No L-dependence is resolved for L ≥ 12. **At L=8 there is a −1.1(3)% (c=0.3) / −1.2(6)% (c=0.4) residual (3.6σ / 2.1σ).** It is the same at both c (difference −0.0008(33)) and drives a 2.4σ preference for a 1/L² term. It can be either a genuine O(a²) tree-level mismatch in N̂_T or the O(g0⁴) contamination −0.02·b(L) with a cutoff-dependent b. The two-β design cannot tell these apart, and the earlier L12 β=30 probe does not constrain b (an exact 3-β solve gives b = 1.8 ± 1.7). **So δ(L) is not cleanly zero: it is ≤ 0.5% for L ≥ 12, with a ~1% (3.6σ) deviation at L=8.** L=6, the coarsest step-scaling lattice, was not in A2. Its only check is β = 2000: 0.996(13) at c=0.3, 1.003(26) at c=0.4.
* Impact on pair shifts, if such a δ persisted unchanged to u ≈ 2: Δs ≈ (δ(2L) − δ(L))/u = +0.0020(27) for 8→16 and +0.0029(32) for 12→24 at u = 2. That is not significant, but it is not small against the per-pair statistical errors (0.0012–0.0017). A pure a²-type δ = d2/L² would be absorbed by the a²-continuum forms; a non-a² part would not.
* Cross-check A(L) = (R20 − R40)/0.1 = a + 0.3b (c=0.3): 0.515(23), 0.519(28), 0.575(30), 0.538(36). One-loop running predicts Δa(8→24) = 2b0 ln3 = 0.102. The observed ΔA is +0.023(42), 1.9σ low; L=24 β=20 is the least reliable point (below).
* τ_int (units of sep = 10 sweeps): L=16: 0.50 / 0.50 (β20) and 0.50 / 0.62 (β40). L=24: 0.50–0.66 at c=0.3 and 0.50–0.86 at c=0.4 (largest: L24 β20 wca 0.66 / 0.86). Elsewhere 0.50–0.56. The bootstrap, Γ and jackknife errors agree within about 20%.
* **L=24 chain consistency:** at β=40 the 3 chains agree (χ² = 1.4/2 and 1.6/2). **At β=20, c=0.3, they do not: χ² = 7.9/2 (p = 0.019; wca is 2.7σ above wcb).** The between-chain error of the pooled mean is 0.0065, against a bootstrap error of 0.0029. The half-z values within each chain are all below 1.2. This could be a slow long-wavelength mode that a 200-measurement chain does not sample, or a ~2.5σ fluctuation. The Birge-inflated variant above covers it, and the A2 conclusions do not change.
* Thermalisation (cold twist-eater start, therm 500): the plaquette plateaus within the first third of therm, and no first/second-half |z| exceeds 1.8. Topology: max|Q| ≤ 2.4·10⁻⁴ at weak coupling, with no |round Q| ≥ 1 anywhere.

## B: 4th u ≈ 2.0 (β* = 3.658 / 3.785 / 3.929) plus prod5 (u ≈ 1.5, 2.4, 2.9): 4-u twisted step scaling
The tuning hit: g²(L6, 3.658) = 2.0062(35), g²(L8, 3.785) = 1.9991(35), g²(L12, 3.929) = 2.0138(51) (c=0.3).
The u≈2.0 pair shifts (c=0.3 | c=0.4) are 6→12 0.0706(13) | 0.0675(24), 8→16 0.0702(14) | 0.0746(27), 12→24 0.0678(17) | 0.0669(34). The exact two-loop values are 0.0698 | 0.0702 (one-loop 0.0644).
**Check:** the script run on the prod5 3 u only (`_3u_check`) reproduces S6 exactly (k1 −0.0025(27) / −0.0019(46), c-gap +0.0017(10)).

**Continuum s at u ≈ 2.0** (c=0.3 | c=0.4): lin 0.0676(20) | 0.0716(40) [χ² 0.5/1 | 4.5/1, from the high 8→16 point at c=0.4]; T1.636 0.0678(19) | 0.0716(37); quad 0.0645(48) | 0.0531(96); Q1.636 0.0648(45) | 0.0547(88).

**Continuum c-gap s(0.4) − s(0.3), correlated, weighted over the 4 u:**
* a²-type forms: T1.636 **+0.0020(9) (+2.3σ)**, lin +0.0022(9) (+2.4σ). Per u (T1.636): −0.0006(25), +0.0039(21), +0.0022(16), +0.0019(13). The prod5 3-u value was +0.0017(10).
* a⁴ forms: quad −0.0041(23) (−1.7σ), Q1.636 −0.0035(21) (−1.7σ).
* Same-u variant (c=0.4 moved to the c=0.3 u with the two-loop slope): T1.636 +0.0014(9), quad −0.0047(23).
* Finest pair, 12→24, pair-level gap per u: −0.0029(24), −0.0009(20), +0.0007(15), +0.0002(12); weighted ≈ −0.0002(8). There is still no c-gap at the finest pair.
* Comparison: periodic Wilson +0.0047(11), periodic Zeuthen +0.0026(11) (T1.636).

**k1 (s = s0 + k1 u + k2 u², s0 = 2b0 ln2 fixed, GLS with the bootstrap covariance over the 4 u; k2 free now leaves 2 dof):**

| form, k2 | k1 c=0.3 | k1 c=0.4 | Δk1 (corr.) | χ² (2 dof / 3 dof) |
|---|---|---|---|---|
| **T1.636 (HMS, a²), k2 free: primary** | **−0.0004 ± 0.0021** (−0.2σ from 0, −1.4σ from 0.0026) | **+0.0013 ± 0.0035** (+0.4σ, −0.4σ) | +0.0016(18) (+0.9σ) | 2.5, 2.3 |
| lin (a²), k2 free | −0.0007 ± 0.0023 | +0.0008 ± 0.0038 | +0.0015(20) | 2.6, 2.3 |
| quad (a² + a⁴), k2 free | −0.0004 ± 0.0056 | −0.0117 ± 0.0096 | −0.0113(49) (−2.3σ) | 0.6, 1.3 |
| Q1.636 (HMS + a⁴), k2 free | −0.0002 ± 0.0052 | −0.0103 ± 0.0088 | −0.0101(45) (−2.2σ) | 0.6, 1.3 |
| T1.636, k2 = 0 | +0.00099 ± 0.00034 | +0.00170 ± 0.00059 | +0.0007(3) | 3.0, 2.4 |
| lin, k2 = 0 | +0.00082 ± 0.00037 | +0.00163 ± 0.00064 | +0.0008(3) | 3.0, 2.4 |
| quad, k2 = 0 | +0.0017 ± 0.0009 | +0.0003 ± 0.0016 | −0.0014(8) | 0.8, 3.0 |
| Q1.636, k2 = 0 | +0.0017 ± 0.0008 | +0.0005 ± 0.0014 | −0.0012(7) | 0.7, 2.9 |

The joint common-k1 fit (8×8 covariance) gives T1.636 k2 free −0.0016 ± 0.0016 (χ² 3.5/5), lin −0.0018(18), quad +0.0083(43) (7.2/5), and T1.636 k2 = 0 +0.00046(25). These are not inputs to the rule.
The σ(k1) the S7 projection predicted for a ×1 point at u = 2.0 (0.0022 / 0.0035) is what we got (0.0021 / 0.0035).

**Stopping rule (ORIGINAL, unchanged; primary T1.636, k2 free, both c).** TWO-LOOP-consistent needs |k1 − 0.0026| ≤ 2σ AND |k1| ≥ 3σ at both c. Here |k1|/σ = 0.2 and 0.4: no. ONE-LOOP-consistent needs |k1| ≤ 2σ AND |k1 − 0.0026| ≥ 3σ at both c. Here the distances from 0.0026 are 1.4σ and 0.4σ: no.
**Verdict: UNDECIDED.** It is UNDECIDED for every form, with k2 free and with k2 = 0, and in every sensitivity variant.
Precision requirements:
(1) σ(k1) ≤ 0.0009: **FAIL** (0.0021 / 0.0035).
(2) c=0.3/0.4 agree within 2σ, correlated: **PASS** (+0.9σ).
(3) Form spread below σ: **FAIL**. At c=0.3 it now passes (0.0004 vs 0.0021). At c=0.4 it fails (0.0131 vs 0.0035), driven by the a⁴ forms at u ≈ 1.5 and 2.0.

**Sensitivity (T1.636 k2 free, c=0.3 / 0.4; all UNDECIDED):**
* Blocks of 20: −0.0004(21) / +0.0014(36).
* The L24 β=3.929 chains twd and twe differ by +2.6σ (c=0.3) and +2.5σ (c=0.4). Dropping twe gives −0.0019(23) / −0.0007(38); dropping twd gives +0.0010(23) / +0.0038(38).
* Continuum N_T instead of N̂_T: −0.0067(22) / +0.0011(37). That variant fails requirement (2) at 4.2σ and gives c-gap +0.0058(9). So the a²-form results depend on N̂_T being right, which is what A2 tests (see A2: fine for L ≥ 12 at ≲ 0.5%, a ~1% question mark at L=8, L=6 untested).

## Thermalisation, autocorrelation, topology (B ensembles; S8_tw6_checks.md)
* First/second-half z over all 57 (job, observable) values: max |z| = 1.80; none above 2.
* Chain pairs at L=24: the u≈2.0 β=3.929 twd/twe pair differs by +2.64σ / +2.53σ (flag above). Neither chain drifts internally (half-z ≤ 0.5).
* τ_int: L24 β3.929 0.65–0.84 (c=0.3) and 1.03–1.11 (c=0.4); L16 β3.785 0.71 / 0.98; others 0.50–0.64.
* Cold (twist-eater) start: the plaquette plateaus within the first third of 300 therm sweeps (L24: last-100-therm minus measurement mean ≤ 2·10⁻⁵).
* Topology: max|Q| = 0.013 (L6), ≤ 1.3·10⁻³ at L=24, no |round Q| ≥ 1, 0 sector changes. Every chain is in Q = 0. With n_12 = 1 only, Q is integer-valued.

## Caveats
* **Finite volume / scheme.** The TGF is a finite-volume scheme; s, N_T(c) and k2 depend on c and on the twisted box (n_12 = 1 in plane (0,1), directions 2 and 3 periodic and untwisted). Only s0 and k1 are universal.
* **Wrap-around.** At c = 0.4 the smoothing radius √(8t) = 0.4L wraps around the box. N̂_T includes all images exactly only at tree level; higher-order wrap-around effects are part of the scheme and the cutoff effects. At L = 6 and 8, √(8t) is only 1.8–3.2 lattice spacings, so the 6→12 pair carries large cutoff effects.
* **Q = 0 / cold starts.** No chain left Q = 0, and the Q-dependence in the twisted box is not measured.
* **Continuum forms.** The a⁴ forms are exact (0 dof), with errors 2–3× larger.
* **Statistics and design.** There are 2 chains per L=24 point at u≈2.0, and they are 2.6σ apart. k1 and k2 stay highly anti-correlated. The two-loop reference at large u is indicative.
* **A2 design.** A2 cannot separate δ_tree from O(g0⁴), and L=6 is not covered.

## Resources
* **Production (prod6).** CPU = sum of per-process elapsed at the final stderr line (single-threaded, niced 19; an upper bound): **18.99 CPU-h** (L=24 16.14, L=16 2.05, L=12 0.68, L=8 0.11, L=6 0.01). The estimate was 19.83 and the caps summed to 24.97.
* Wall time: queue 13:43:05 → 20:05:22 PDT = 6 h 22 min, maxp 3.
* Pre-launch: 16 cores (hw.ncpu), 64 GiB, load 8.39 / 7.99 / 8.66, memory free 68%, 0 su2gf processes.
* Guard log `prod6/resource_guard6_prod.log.txt` (copy of the run-dir log) (30 s): 805 samples, 13:43:05–20:25:47 PDT. load1 min 5.59 / max 19.26 / mean 10.94 (> 16 in 5 samples). Free RAM (memory_pressure) 61–71% (free + inactive ≥ 19.4 GiB). Our processes: 3 in 756 samples, 2 in 1, 1 in 6, 0 in 42. State: run 800, **throttled_1proc 5 (0.6%)**, paused 0.
* **Analysis (this report).** On the Mac, niced 19, one single-threaded python process at a time (about 98% of one core). Pre-run 20:55 PDT: 16 cores, load 7.49 / 7.00 / 7.18, memory free 64%, 0 su2gf processes. The final regeneration is logged in `resource_analysis_prod6.log.txt` (30 s, 10 samples 21:02:32–21:07:02 PDT, load1 7.23–10.40, free RAM 60–63%; its py= column sums all python processes on the machine, including other users' unrelated jobs, which were not touched). Total analysis CPU is about 15 min (< 0.3 CPU-h). No MC was launched.
