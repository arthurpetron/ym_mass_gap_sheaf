# SLICE-AMP(1/2): statement, certificate design, and feasibility (YB-14 Phase 4 continued, 2026-11-27)

**Scripts:** box-only, `/workspace/novel_paths/yb14/` (`single_link_kappa.py`, `slice_scan.py`, `slice_scan2.py`, `be_opt2.py`); not committed (docs-only).

**Label: paper design + box numerics. No Lean. NOT gap evidence.**
Base for this note: origin/main **d2e975b5** (d1f4bd41 plus `DobrushinNeumann.lean`). Builds on
`audits/PHASE4-LOG-2026-11-27.md` and `audits/SCOPE-SLAB-CURVATURE-2026-11-27.md`.

Measurements below are **lower bounds** on Wasserstein influences (first-moment / dual) or **upper bounds**
on Bakry–Émery infima (found configurations). Nothing here discharges `hfine_T2_half_OPEN`.

## 1. The statement

### 1.1 The 3D slice measure
On the spatial links of a time-slice (the infinite lattice ℤ³, or a large box of width W with
lateral boundary conditions), with two frozen neighbouring slices V, V′, the repo's temporal-gauge
conditional measure at nome w is

> μ_{V,V′}(dU) ∝ [ Π_{spatial plaquettes p} f_w(U_p) ] [ Π_ℓ f_w(U_ℓ V_ℓ⁻¹) f_w(U_ℓ V′_ℓ⁻¹) ] Haar(dU),

with f_w = Σ_s (s+1) w^{s(s+2)} χ_s (repo `coeffW`). At step 2, w = 1/2 and u = w³ = 1/8.

The metric on configurations is the **product geodesic metric**, d(U,Ũ) = Σ_ℓ d_{S³}(U_ℓ, Ũ_ℓ).
W₁ is the 1-Wasserstein distance for that metric. (Step 1 used this geodesic convention;
`hDobW1_OPEN` is the remaining analytic input there.)

### 1.2 SLICE-AMP(1/2)
**Statement.** There is a constant κ_* ≤ κ_budget such that for every V, V′ and every Ṽ that
differs from V at a single link ℓ₀,

> W₁( μ_{V,V′}, μ_{Ṽ,V′} ) ≤ κ_* · d_{S³}(V_{ℓ₀}, Ṽ_{ℓ₀}).

The same bound is required with the roles of V and V′ swapped. The constant is independent of the
spatial width W (and of the lateral boundary, if the slice is a finite box). This is a worst-case
bound over all kinetic boundaries, not a typical-case estimate.

### 1.3 The exact TB-DOB budget at step 2
One-sided time weights (`steps01_uniform.md` §9.1) give a slice-to-slice Dobrushin sum
α = κ_* (e^m + e^{−m}). The two-step factor 1/128 needs e^{−4m} ≤ 1/128, i.e. e^m ≥ 128^{1/4}.

- 128^{1/4} ∈ (52556/15625, 336359/100000), i.e. (3.363584, 3.363590), by comparing fourth powers
  in exact rationals.
- The exact budget is B = 1/(128^{1/4} + 128^{−1/4}) ∈
  (33635900000/123137376881, 821187500/3006273761) ⊂ (0.2731575, 0.2731579).

**Rational working targets** (each is a legal κ_* ceiling for a rational rate R with R⁴ ≥ 128, so
e^{−4m} = R^{−4} ≤ 1/128):

| R (set e^m = R) | R⁴ | allowed κ_* = R/(R²+1) | decimal |
|---|---|---|---|
| 336359/100000 | 128.00066 | 33635900000/123137376881 | 0.2731575 (tight) |
| 27/8 = 3.375 | 129.746 | **216/793** | **0.272383** (recommended) |
| 17/5 = 3.4 | 133.634 | 85/314 | 0.270701 |
| 3 | 81 < 128 | — | too small; misses the two-step factor |

The recommended Lean-facing target is

> **κ_* ≤ 216/793**  (R = 27/8).

The looser 27/100 = 0.27 is also valid and leaves a 0.003 margin. 273/1000 = 0.273 is valid against
the tight enclosure of B, but the margin is only 1.6·10⁻⁴ and needs the fourth-power comparison
above to be formalised.

**Amplification form (heuristic only).** If κ_kin is an upper bound on the single-link kinetic
influence, the budget allows A := κ_*/κ_kin ≤ 216/793 κ_kin⁻¹. With the typical |dE| ≈ 0.11–0.12
this is A ≲ 2.3, which was the Phase-4 slogan; it is **not** the official constant. The official
constant is κ_* itself. A certified κ_kin (see §3) would convert the two.

### 1.4 How this implies `fineAt` at step 2
If SLICE-AMP(1/2) holds at 216/793, the slice-block matrix with one-sided time weights has
weighted row sum α ≤ (216/793)·(27/8 + 8/27) = 1, and in fact < 1 because 216/793 is a strict
ceiling. `DobrushinNeumann.cpow_resolvent` (on the 1-dimensional time chain of slices, or on the
full 3+1 Dobrushin matrix) plus the existing Föllmer / log-convexity / `twoStepFactor_of_even_decay`
chain of `steps01_uniform.md` §3 would give `fineAtT W 2 (1/128)` for every W. The Föllmer step
and the W₁ comparison itself remain OPEN (`hDobW1_OPEN` at step 1 already).

**U(1) verdict:** SLICE-AMP and this implication are **U(1)-true** at matched activity. They are
not non-abelian evidence. (Matched U(1) is confined at w = 1/2.)

## 2. Certificate design

The aim is a finite, constructive, compactness-free certificate of the bound in §1.2.

### 2.1 Architecture
1. **Local bound.** For a finite block B of spatial links (a cube of side L, a plaquette, or a
   1- or 2-link cluster) and for every environment η of B (the spatial halo plus the kinetic
   fields V, V′ on B), bound the W₁ response of μ_B(·|η) to a change of one neighbouring site,
   uniformly in η.
2. **GRID-SUP, not compactness.** The map η ↦ I(η) (the influence) is Lipschitz for an explicit
   constant Lip, computed from the second derivative of log f_w and the coordination. A finite
   δ-net of the environment space with Lip·d(η, net) ≤ ε gives a uniform bound from the values
   (or upper bounds) of I on the net. No appeal to compactness of SU(2)^M.
3. **Matrix and resolvent.** The resulting block-to-block (or site-to-site) numbers form a
   nonnegative matrix C on a finite index (the tiling of a large box, or a translation-invariant
   stencil). If a weighted row sum is ≤ α < 1 for a spatial weight ρ ≥ 1, the repo module
   `YMGap.Continuum.DobrushinNeumann` (d2e975b5) supplies, constructively:
   - `cpow` (C^k with `cpow 0 = I`, because `FiniteTransferTrace.tpow k = C^{k+1}`);
   - `cpow_weighted`: (cpow n C k i j) · ρ^{d i j} ≤ α^k;
   - `tpow_weighted`: (tpow n C k i j) · ρ^{d i j} ≤ α^{k+1};
   - `cpow_resolvent`: (Σ_{k<K} cpow n C k i j) · ρ^{d i j} ≤ 1/(1−α) for α < 1.
   The total influence of one kinetic insertion is then ≤ κ_kin · (1 + spatial resolvent), which
   is the κ_* of §1.2.
4. **Width uniformity** is free once the stencil and the constants are W-independent
   (the same mechanism as W27, but now for the interacting 3D slice).

The Föllmer covariance estimate that turns the resolvent into a two-point bound is still
literature / OPEN, as at step 1.

### 2.2 Why single-site Dobrushin is not enough
Even the *smallest* single-link W₁ lower bounds at w = 1/2 are κ ≳ 0.090 (all staples aligned;
§3). Twelve spatial neighbours give 12κ ≳ 1.08 > 1, before the two kinetic terms. The
one-sided-weight criterion (12 κ_sp + (e^m + e^{−m}) κ_kin) is larger still. **A block (or a
different metric / path-coupling) is required.** This is the same obstruction recorded in
Phase 4: 12u = 1.5 > 1 at the heuristic κ ≈ u.

### 2.3 Why a raw net on a 3D box is impossible
A cube of side L has 3L³ links and a kinetic boundary of size M = 2·3L³ plus a spatial halo.
The covering number of S³ at geodesic scale δ is ≳ 2π² / vol(ball of radius δ/2) ≈ 38/δ³
(packing lower bound), and a constructive Hopf-type grid is a few times larger (~40–80/δ³).

For a product ℓ^∞ net the Lipschitz error is ≤ (Lip per factor)·M·δ. Targeting an error of
0.005 (about 2% of the budget) with a conservative Lip per factor of 0.2 already forces δ ≤
0.005/(0.2 M) and the following net sizes (using N = 40/δ³):

| M (SU(2) factors) | δ needed | N per factor | N^M |
|---|---|---|---|
| 2 | 0.0125 | 2·10⁷ | 10^{14.6} |
| 4 | 0.0062 | 1.6·10⁸ | 10^{32.9} |
| 6 | 0.0042 | 5.5·10⁸ | 10^{52.5} |
| 12 | 0.0021 | 4.4·10⁹ | 10^{115} |
| 24 (open 2-cube kinetics only) | 0.0010 | 3.5·10^{10} | 10^{253} |

Even M = 2 is out of reach. Gauge-fixing a spanning tree reduces the *interior* of a block, not
the number of free boundary SU(2)'s by more than a constant factor; the exponential in M remains.
**Enumerating the boundary of a 3D box of any side L is a computational no-go.**

### 2.4 The only plausible computational fragment: a low-dimensional reduction
Step 1 worked because the 1-link environment was reduced to a **resultant staple** (a vector in a
3-ball, and after rotations a 1- or 2-parameter family) plus an explicit remainder for higher
characters. A net in dimension 1–2 is small.

| block | environment after reductions | interior integral | net feasible? | Dobrushin? |
|---|---|---|---|---|
| 1 link | resultant staple, dim 1–2 (plus a higher-character remainder at w = 1/2 of size 9w⁸ = 9/256) | S³ quadrature, ~10⁵ points; already run (§3), seconds per point | **yes** | **no**: 12κ > 1 |
| 2 links sharing a plaquette | two resultants + relative orientation, dim ~6–8 | SU(2)², or a character-closed formula if one exists | only if the 2-link integral is *closed form* (a 6D net of cheap points might be 10⁷–10⁹; a nested quadrature is not) | unknown: the block degree may still be large |
| 1 plaquette (4 links), tree gauge | 1 leftover SU(2) interior; halo still high-dimensional | 3D after gauge fixing, cheap per net point | only after a further staple-resultant reduction of the halo | unknown |
| cube of side L ≥ 2 | M = Θ(L²) halo links | SU(2)^{Θ(L³)}, impossible to integrate | **no** | — |

**Go/no-go on a certificate, by L.**

- **For every L: a GRID-SUP certificate that enumerates the raw boundary of a 3D cube of side L is not computationally reachable.** This is the honest answer to “at what L is a box certificate reachable?”: at none.
- **A certificate is not ruled out**, but it has to be of the step-1 kind: a *small* block (1–2 links, or one gauge-fixed plaquette), an analytical or character-closed interior, a low-dimensional sufficient statistic, a net in dimension ≲ 3, and then `cpow_resolvent` to lift. Whether any such small block has a Dobrushin constant < 1 at u = 1/8 is OPEN and is the correct next math question.
- A 3D cluster / orthogonality expansion is unlikely to substitute: per-face activity z = 2w³ = 1/4, and even a generous 3D plaquette-animal growth (heuristic κ ≳ 10, vs 96 in 4D) gives κz ≳ 2.5 > 1. This is the same arithmetic as `audits/SCOPE-SU2-ORTHOGONALITY-EXPANSION-2026-11-16.md`, which already concluded that step 2 is out of polymer radius in 4D.

Path-coupling with a *configuration-independent* reweighting of the product metric cannot beat 12κ > 1 on a vertex-transitive lattice. A configuration-dependent metric is a different method (close to Bakry–Émery, which fails uniformly on the full SU(2) measure from step 1; see the curvature scope).

### 2.5 What a Lean module would look like, if the small-block constant were proved
An additive `YMGap.RG.SliceAmpStep2` that takes as OPEN or proved input a uniform block-influence
bound, applies `cpow_resolvent`, and feeds `fineAtT` at factor 1/128, in the same style as
`Step0DobrushinUniform` / `Step1DobrushinUniform`. Not proposed until a small-block constant < 1
exists on paper. **U(1)-true.**

## 3. Single-link influences at w = 1/2 (quadrature)

S³ Haar quadrature with exact cell masses (48×32×64, total weight 1). For each 6-staple environment
(4 spatial + 2 kinetic), the score of rotating one staple is integrated: |dE[U]/dθ| (a lower bound
on chordal W₁) and a geodesic KR dual on a 380-point net (a lower bound on geodesic W₁). The TV×π
upper bound is 0.52–0.73, which is above the budget and not useful. **No tight constructive W₁
upper bound was obtained.**

Findings:
- All staples aligned is gauge-equivalent to the identity environment: |dE| = 0.090, W₁ ≥ 0.093.
  This is the *smallest* in the scan, and already 12×0.090 = 1.08 > 1.
- Conflicting staples *raise* the influence (the heat kernel at w = 1/2 is not a pure vMF, for
  which the covariance is maximal at zero field): 4 spatial antipodes + kinetic at 0 gives
  |dE| = 0.136, W₁ ≥ 0.142; 80 random Haar 6-tuples give kinetic W₁ ≥ up to **0.148**
  (mean 0.129). Extra hostile 6-direction / 3+3 families did not beat 0.148.
- So the worst *found* single-link lower bound is ≈ 0.15, still well below 0.273. The official
  κ_* could in principle be violated only by in-slice amplification, or by a worse environment
  than those sampled, or by the gap between the dual lower bound and the true W₁.

These are not a uniform certificate (the 6-staple space was sampled, not netted). A 1-link
GRID-SUP in the resultant-staple reduction remains feasible and would be the natural way to
certify a κ_kin upper bound (analogous to the 7/20 certificate, with a larger character
remainder 9w⁸ = 9/256).

## 4. Slice-level Monte Carlo (V2; worst-case still unproved)

Quantity: the linear response of E[U_ℓ] (ℝ⁴) to an infinitesimal geodesic rotation of one
kinetic boundary link, summed in the product-chordal metric, Σ_ℓ ||Cov(U_ℓ, score)||. This is a
**lower bound** on the product-W₁ Lipschitz constant (the official κ_* is geodesic). Periodic
L³ is a probe, not the official infinite-volume slice; wraparound at L = 2 is the most severe
geometry.

A first L = 2 scan at 400 sweeps produced totals up to 0.38, several of them above the budget.
Those numbers are **not** used: the sum of 23 off-diagonal magnitudes is dominated by the
expectation of ||noise|| (≈ 23 × 0.94 σ). The production scan jackknifes the *scalar* total,
reports a 2σ-thresholded total (`tot2s`), and uses 8000 sweeps at L = 2 and 4000 at L = 3.

### 4.1 L = 2, 8000 sweeps (production)

16 kinetic boundaries, periodic 2³ (24 links), 8000 Metropolis sweeps (thermalisation = 1/5), jackknife SE
from 20 batches. `tot2s` is direct plus off-diagonal links with ||Cov|| > 2σ. Elapsed 1035 s.

| tag | direct | TOTAL (jackknife) | tot2s | n2 | n3 | A_raw |
|---|---|---|---|---|---|---|
| aligned | 0.1123±0.0015 | 0.2006±0.0101 | 0.1123 | 0 | 0 | 1.79 |
| antialigned-both | 0.1139±0.0019 | 0.1933±0.0088 | 0.1139 | 0 | 0 | 1.70 |
| aligned-vs-anti | 0.1273±0.0017 | 0.2186±0.0093 | 0.1273 | 0 | 0 | 1.72 |
| pi-flux-both | 0.1146±0.0017 | 0.1874±0.0067 | 0.1146 | 0 | 0 | 1.64 |
| pi-flux-vs-aligned | 0.1123±0.0016 | 0.1947±0.0070 | 0.1184 | 1 | 0 | 1.73 |
| twist-x-both | 0.1179±0.0023 | 0.2027±0.0050 | 0.1305 | 2 | 0 | 1.72 |
| V-ang-pi2-vs-1 | 0.1246±0.0014 | 0.1966±0.0098 | 0.1246 | 0 | 0 | 1.58 |
| V-ang2.5-vs-1 | 0.1288±0.0022 | 0.2176±0.0113 | 0.1288 | 0 | 0 | 1.69 |
| V-ang-pi-vs-1 | 0.1331±0.0017 | 0.2239±0.0115 | 0.1331 | 0 | 0 | 1.68 |
| V-ang2-vs-inv | 0.1307±0.0019 | 0.2254±0.0080 | 0.1307 | 0 | 0 | 1.72 |
| haar-0 | 0.1266±0.0017 | 0.2134±0.0109 | 0.1357 | 1 | 0 | 1.69 |
| haar-1 | 0.1204±0.0018 | 0.1968±0.0066 | 0.1204 | 0 | 0 | 1.63 |
| haar-2 | 0.1203±0.0018 | 0.2058±0.0073 | 0.1203 | 0 | 0 | 1.71 |
| haar-3 | 0.1220±0.0022 | 0.2192±0.0104 | 0.1220 | 0 | 0 | 1.80 |
| haar-vs-aligned | 0.1237±0.0021 | 0.2066±0.0080 | 0.1237 | 0 | 0 | 1.67 |
| random-Z2-both | 0.1157±0.0013 | 0.1844±0.0048 | 0.1157 | 0 | 0 | 1.59 |

Max `tot2s` = 0.1357 (haar-0). Max raw TOTAL = 0.2254. Direct range 0.1123–0.1331. No 3σ off-diagonal
anywhere; the three n2 = 1 or 2 hits are at the 2σ edge (with 23 tests, a few such hits are expected).

### 4.2 L = 3, 4000 sweeps (production)

16 boundaries, periodic 3³ (81 links). Elapsed 1735 s.

| tag | direct | TOTAL (jackknife) | tot2s | n2 | n3 | A_raw |
|---|---|---|---|---|---|---|
| aligned | 0.1122±0.0028 | 0.4768±0.0269 | 0.1122 | 0 | 0 | 4.25 |
| antialigned-both | 0.1134±0.0026 | 0.4733±0.0187 | 0.1134 | 0 | 0 | 4.18 |
| aligned-vs-anti | 0.1354±0.0017 | 0.5564±0.0318 | 0.1475 | 1 | 0 | 4.11 |
| pi-flux-both | 0.1127±0.0018 | 0.4738±0.0283 | 0.1213 | 1 | 0 | 4.20 |
| pi-flux-vs-aligned | 0.1134±0.0023 | 0.4847±0.0239 | 0.1134 | 0 | 0 | 4.28 |
| twist-x-both | 0.1140±0.0023 | 0.4877±0.0175 | 0.1331 | 2 | 0 | 4.28 |
| V-ang-pi2-vs-1 | 0.1218±0.0028 | 0.4989±0.0235 | 0.1218 | 0 | 0 | 4.10 |
| V-ang2.5-vs-1 | 0.1288±0.0030 | 0.5333±0.0269 | 0.1288 | 0 | 0 | 4.14 |
| V-ang-pi-vs-1 | 0.1278±0.0024 | 0.5818±0.0251 | 0.1278 | 0 | 0 | 4.55 |
| V-ang2-vs-inv | 0.1317±0.0030 | 0.5759±0.0272 | 0.1317 | 0 | 0 | 4.37 |
| haar-0 | 0.1246±0.0021 | 0.5131±0.0270 | 0.1246 | 0 | 0 | 4.12 |
| haar-1 | 0.1205±0.0029 | 0.4860±0.0166 | 0.1205 | 0 | 0 | 4.03 |
| haar-2 | 0.1216±0.0030 | 0.5011±0.0197 | 0.1216 | 0 | 0 | 4.12 |
| haar-3 | 0.1229±0.0025 | 0.5169±0.0238 | 0.1327 | 1 | 0 | 4.20 |
| haar-vs-aligned | 0.1268±0.0034 | 0.5369±0.0235 | 0.1268 | 0 | 0 | 4.23 |
| random-Z2-both | 0.1147±0.0027 | 0.4813±0.0214 | 0.1147 | 0 | 0 | 4.20 |

Max `tot2s` = 0.1475 (aligned-vs-anti). Direct range 0.1122–0.1354. Raw TOTAL is 0.47–0.58, *above*
the budget, and A_raw ≈ 4: both are the sum of 80 sub-threshold magnitudes. The expected noise
floor is ≈ 80 × 0.94 × σ with σ ≈ 0.005, i.e. ≈ 0.38, plus the direct term ≈ 0.12, giving ≈ 0.50,
which matches the raw TOTAL. **Raw TOTAL and A_raw are not used as evidence for or against the bound.**

### 4.3 L = 4 skipped
A production L = 4 scan (192 links) was not run. A reduced 6-boundary job at 2500 sweeps would have
fitted in about 15 wall-clock minutes and within the 2 CPU-h / 1 GiB limits, but it would not have
changed either verdict: the raw GRID-SUP certificate is already a no-go at every L (§2.3), and the
L = 2 and L = 3 probes already agree that `tot2s` stays at the direct term (max 0.15 ≪ 0.273) while
raw TOTAL grows like (3L³ − 1) × σ, as a sum of noise magnitudes. L = 4 would only have made that
noise worse.

### 4.4 Reading
Across all 32 high-statistics boundaries at L = 2 and L = 3:

- The honest lower bound on κ_* is `tot2s`, and the maximum seen is **0.1475**, about half of
  216/793 ≈ 0.272. The direct term itself is 0.11–0.14, consistent with the single-link
  quadrature (§3).
- No in-slice amplification is visible above noise. The few n2 = 1 or 2 counts sit at the 2σ
  edge; n3 = 0 everywhere.
- Low-statistics L = 2 totals that appeared to exceed the budget (up to 0.38 at 400 sweeps) were
  noise, as predicted by the magnitude-sum model, and did not reproduce at 8000 sweeps
  (`tot2s` ≤ 0.136).
- This does **not** prove the worst-case bound: the boundary space was sampled (structured
  families, Haar, Z₂, opposed kinetics), not netted. It does mean SLICE-AMP at 216/793 has not
  been numerically refuted on these probes, including on the L = 2 torus (the most wraparound).

A genuine numerical no-go would be a boundary with `tot2s` (or TOTAL after a noise subtraction,
at several standard errors) above 0.273. That has not been seen.

**U(1):** this probe is group-agnostic.

## 5. SO(3)-part Bakry–Émery, robustness

Searches for λ_min(Ric + Hess of the even-spin action) at w = 1/2. Every number is an **upper bound
on the infimum**. A positive value does not prove SO3-BE. A negative value would refute a uniform
lower bound of 0 at that lattice size. None was found.

| search | lattice | method | best λ_min found |
|---|---|---|---|
| `be_opt.py` (earlier) | L=2, N=2 | random local min + π/2 seeds | +1.0867 |
| `be_opt.py` (earlier) | L=4, N=2 | same | +1.1834 |
| `be_opt2.py` | L=2, N=2 | annealing, 14 starts (incl. π/2) | +1.1823 |
| `be_opt2b.py` | L=2, N=2 | tighter π/2 packing (8 seeds, 4000 drive steps) + descent | **+1.0593** |
| `be_opt2b.py` | L=3, N=2 | 3 π/2 seeds + 2 random | +1.1715 |

The tighter L = 2 packing reached mean|cos ψ| = 0.010 (cost 0.012) and then descended to 1.0593.
All other L = 2 starts (about 30 in total across the three searches) landed in 1.06–1.33. On L = 3
the π/2 packing is poorer (mean|cos ψ| ≈ 0.05) and the best found value is higher, 1.17, consistent
with L = 4. So **+1.06 is a robust upper bound on the infimum** at this volume: a broader search did
not go negative, and did not even go below 1. The previous “≈ +1.1” stands, slightly improved.

It is still only an upper bound. The crude configuration-uniform lower bound remains −0.55
(`SCOPE-SLAB-CURVATURE` §4), so the sign of the true infimum is not proved. SO3-BE at w = 1/2 stays
OPEN as a complement, and only together with Z2-VORTEX (activity up to 0.48, where Dobrushin fails).

U(1): SO3-BE is U(1)-false; Z2-VORTEX is U(1)-analogous.

## 6. Verdicts and queue

| claim | status | U(1) |
|---|---|---|
| SLICE-AMP(1/2) at κ_* ≤ 216/793 | **OPEN** (not refuted by high-stat probes, max `tot2s` = 0.148; not proved) | U(1)-true |
| raw GRID-SUP on a 3D box of any L | **NO-GO** (computational, §2.3); L = 2, 3, 4 alike | n/a |
| 1-link Dobrushin at w = 1/2 | **NO-GO** (12κ > 1, §2.2–3) | U(1)-true |
| small-block (2-link / plaquette) + `cpow_resolvent` | **CANDIDATE**, the only computationally plausible certificate | U(1)-true |
| 3D polymer / orthogonality at u = 1/8 | predicted not to converge (heuristic) | U(1)-true at matched z, not evidence |
| SO3-BE at w = 1/2 | OPEN; best found λ_min = +1.0593, still only an upper bound on the inf | U(1)-false |
| Z2-VORTEX at w = 1/2 | OPEN, Dobrushin fails | U(1)-analogous |

**Feasibility by L** (raw box certificate vs MC probe):

| L | raw net (kinetic boundary alone) | per-boundary exact integral | MC probe | box certificate |
|---|---|---|---|---|
| 2 | M = 24, N^M ~ 10^{253} at a 0.005 error | SU(2)^{12} interior, impossible | 16 boundaries, 8000 sweeps, 1035 s; max `tot2s` = 0.136 | **NO-GO** |
| 3 | M = 162, worse | worse | 16 boundaries, 4000 sweeps, 1735 s; max `tot2s` = 0.148 | **NO-GO** |
| 4 | worse | worse | skipped, would not change the no-go | **NO-GO** |
| any L | M = Θ(L³) | impossible | — | **NO-GO** |

**Queue.** (1) A paper bound, or a resultant-staple GRID-SUP, for a 2-link or one-plaquette
influence constant at u = 1/8 — this is the only route that could make SLICE-AMP a certificate.
(2) Optional: a 1-link GRID-SUP for a certified κ_kin (useful, not sufficient). (3) SO3-BE remains
a complement only, and only together with Z2-VORTEX. (4) `cpow_resolvent` is already in the repo
at d2e975b5; no further Neumann algebra is needed.

## 7. Resources
All jobs: `prlimit --as=1 GiB`, `OMP_NUM_THREADS=1`, `python3 -P`, one heavy job at a time.
Peak RSS of the jobs themselves was about 50–140 MiB (slice_scan2 ≈ 120 MiB; be_opt2b ≈ 136 MiB).
No Lean was run on the box.

| job | wall / CPU | notes |
|---|---|---|
| `single_link_kappa.py` (w = 1/2 + hostile extras) | 66 s + 9 s | S³ quadrature |
| `slice_scan.py` L=2 smoke (400 sweeps; discarded) | 180 s (timeout, no summary) | noise-dominated; not used |
| `slice_scan2.py` L=2, 8000 sweeps, 16 boundaries | 1035 s | production |
| `slice_scan2.py` L=3, 4000 sweeps, 16 boundaries | 1735 s | production |
| `be_opt2.py` L=2,N=2 | 49 s | 14 starts |
| `be_opt2b.py` L=2,N=2 | 60 s | tighter π/2 packing |
| `be_opt2b.py` L=3,N=2 | 50 s | volume check |
| L=4 slice scan | not run | see §4.3 |

Production scans plus SO3-BE and quadrature: about 53 CPU-min, well under 2 CPU-h per job and in total.
Box load peaked around 2.5 during the L=3 scan; 10–13 GiB was typically available (the box itself had
other residents). No stray processes were left after the wrap-up.
