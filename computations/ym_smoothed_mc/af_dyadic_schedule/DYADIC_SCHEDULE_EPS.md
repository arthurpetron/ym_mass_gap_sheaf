# Dyadic β-schedule and the εⱼ recompute (0⁺⁺/√σ proxy)

**Lit/MC only, not proof.** Nothing here constructs an intertwiner Φⱼ, measures a
VacSq rate, or proves summability or AF.
Date: 2026-10-06. Path: `computations/ym_smoothed_mc/af_dyadic_schedule/`.
Repro: `python3 dyadic_schedule_eps.py` (stdout saved in `dyadic_schedule_eps_stdout.txt`).

**Single source of truth:** a√σ(β) comes from importing
`../af_nome_asqrt/af_nome_asqrt_schedule.py` (a10b9ea4). That module uses the FHK/UKQCD
knots, ln-linear interpolation in [2.20, 2.85], the lit-slope extrapolation
below 2.20, and the two-loop SU(2) Wilson ratio from the β = 2.85 anchor above 2.85.
μ and the ε formulas come from importing `../af_nome_eps/af_nome_eps_intertwiner.py` (398bac67).

## Formulas

- Dyadic schedule: β^dy_{j+1} solves a√σ(β) = a√σ(β^dy_j)/2 by bisection (a√σ is monotone). The tag is set by the region β lands in: extrap (< 2.20), interp ([2.20, 2.85]), or two-loop (> 2.85).
- Nome: w = exp(−1/(2β)), so β = 4/g² and g² = −8 ln w.
- afNome: 1−w_j^AF = A/(j+κ⌊log₂(j+1)⌋+4), with A = 1.942 and κ = 51/121.
- **Anchors are a convention.** Primary: β^dy_4 = β^AF_4 = 2.016449. Sensitivity check: β^dy_6 = β^AF_6 = 2.533485, solving both up and down from j = 6.
- Proxy (same as 398bac67): Δ_j = μ·a√σ_j and λ_j = e^{−Δ_j}, with μ = 3.78(7) (LTW04). λ is a continuum-inspired **proxy** for r_j, not a measured rate.

## Two-loop asymptotic halving step (derived)

With g² = 4/β, b₀ = 11/(24π²), b₁ = 17/(96π⁴):
ln(aΛ) = −(b₁/2b₀²)·ln(4b₀/β) − β/(8b₀).
Requiring a(β+Δβ)/a(β) = 1/2 gives

  Δβ = 8b₀ ln2 + (4b₁/b₀)·ln(1+Δβ/β) → **Δβ_∞ = 8b₀ ln2 = 11 ln2/(3π²) = 0.257512** as β → ∞,

with a slow correction of about (4b₁/b₀)·Δβ_∞/β ≈ 0.040/β. Exact two-loop halving steps: 0.2718 at β = 2.85, 0.2711 at 3.0, 0.2677 at 4.0, 0.2616 at 10, and 0.2579 at 100.
For comparison, the afNome smooth step is ≈ 1/(2A) = 0.257467. Equivalently, A = 1.942 matches A* = 3π²/(22 ln2) = 1.941659 to 2·10⁻⁴. So afNome uses the **β → ∞** halving step. At finite β (3–4), the true two-loop halving needs about 0.27, so afNome under-steps and its a-ratio sits near 0.518 > 1/2. This is consistent with a10b9ea4. Inside the lit window, the dyadic steps are only 0.21–0.24 because the running is faster than two-loop (AS violation). The first step, in the extrap region, is 0.288.

## Schedule table (anchor j = 4, primary)

| j | β^dy | a√σ | src | w^dy | 1−w^dy | β^AF | Δβ = β^dy−β^AF | Δw | (1−w^dy)/(1−w^AF) | step β^dy | step β^AF |
|--:|-----:|----:|-----|-----:|-------:|-----:|---------------:|---:|------------------:|----------:|----------:|
| 4 | 2.016449 | 0.72834 | extrap | 0.780391 | 0.219609 | 2.016449 | 0 | 0 | 1.0000 | 0.2876 | 0.2586 |
| 5 | 2.304025 | 0.36417 | interp | 0.804921 | 0.195079 | 2.275087 | +0.0289 | +0.00222 | 0.9888 | 0.2094 | 0.2584 |
| 6 | 2.513406 | 0.18209 | interp | 0.819605 | 0.180395 | 2.533485 | −0.0201 | −0.00129 | 1.0072 | 0.2208 | 0.3670 |
| 7 | 2.734198 | 0.09104 | interp | 0.832877 | 0.167123 | 2.900510 | −0.1663 | −0.00878 | 1.0554 | 0.2434 | 0.2581 |
| 8 | 2.977581 | 0.04552 | two-loop | 0.845420 | 0.154580 | 3.158562 | −0.1810 | −0.00817 | 1.0558 | 0.2712 | 0.2580 |
| 9 | 3.248741 | 0.02276 | two-loop | 0.857353 | 0.142647 | 3.416526 | −0.1678 | −0.00651 | 1.0478 | 0.2700 | 0.2579 |
| 10 | 3.518754 | 0.01138 | two-loop | 0.867538 | 0.132462 | 3.674420 | −0.1557 | −0.00524 | 1.0412 | 0.2691 | 0.2578 |
| 11 | 3.787803 | 0.00569 | two-loop | 0.876339 | 0.123661 | 3.932258 | −0.1445 | −0.00426 | 1.0357 | 0.2682 | 0.2578 |
| 12 | 4.056029 | 0.00285 | two-loop | 0.884022 | 0.115978 | 4.190050 | −0.1340 | −0.00349 | 1.0310 | — | 0.2578 |

For the anchor j = 6 variant (full table in `dyadic_schedule_anchor_j6.csv`), Δβ vs AF is +0.028 / +0.050 / 0 / −0.145 / −0.154 / −0.141 / −0.129 / −0.118 / −0.108 for j = 4…12, and (1−w^dy)/(1−w^AF) ∈ [0.981, 1.048]. Under either anchor, the dyadic and afNome schedules differ by at most about 6% in 1−w. The largest gap comes after afNome's κ-log jump at j = 6→7 (step 0.367). From j ≥ 8, the dyadic schedule runs about 0.11–0.18 in β behind afNome, and that gap shrinks slowly.

## ε recompute on the dyadic schedule (μ = 3.78, anchor j = 4)

| j | Δ_j | λ_j | λ_{j+1}²−λ_j | ε^B | ε^A κ-free | ε^A κ-form = λ_j−λ_j² | κ_j (ε=0) = 1/λ_j | κ_j−1 |
|--:|----:|----:|-------------:|----:|-----------:|----------------------:|------------------:|------:|
| 4 | 2.7531 | 0.06373 | 1.2e−16 | ~0 | ~0 | 0.05967 | 15.692 | 14.692 |
| 5 | 1.3766 | 0.25244 | −3.3e−16 | 0 | 0 | 0.18872 | 3.961 | 2.961 |
| 6 | 0.6883 | 0.50244 | 4.4e−16 | ~0 | ~0 | 0.24999 | 1.990 | 0.990 |
| 7 | 0.3441 | 0.70883 | 1.1e−16 | ~0 | ~0 | 0.20639 | 1.411 | 0.411 |
| 8 | 0.1721 | 0.84192 | 0 | 0 | 0 | 0.13309 | 1.188 | 0.188 |
| 9 | 0.0860 | 0.91756 | 1.1e−16 | ~0 | ~0 | 0.07564 | 1.090 | 0.090 |
| 10 | 0.0430 | 0.95789 | −1.1e−16 | 0 | 0 | 0.04033 | 1.044 | 0.044 |
| 11 | 0.0215 | 0.97872 | −1.1e−16 | 0 | 0 | 0.02083 | 1.022 | 0.022 |

**Verified:** max|λ_{j+1}² − λ_j| = 4.4·10⁻¹⁶ (machine precision; the anchor j = 6 variant matches). Also, κ_j = λ_{j+1}²/λ_j² equals 1/λ_j to a relative 2·10⁻¹⁵. So **the schedule-mismatch part of ε vanishes**: ε^B = ε^A_κ-free = 0, and their Lean S₄ = 2.8·10⁻¹⁵ (rounding noise only).

### Side-by-side: afNome (398bac67) vs dyadic (j→j+1)

| j | ε^A κf / ε^B AF | ε^A κf / ε^B dy | ε^A κ AF | ε^A κ dy |
|--:|----------------:|----------------:|---------:|---------:|
| 4 | 0 | ~0 | 0.0477 | 0.0597 |
| 5 | 0.0488 | 0 | 0.2245 | 0.1887 |
| 6 | 0.1322 | ~0 | 0.3816 | 0.2500 |
| 7 | 0 | ~0 | 0.1473 | 0.2064 |
| **Lean S₄** | **0.626 → 0** | | **3.201** | **3.088** |

For κ-free and Shape B, 100% of the 398bac67 ε was schedule mismatch. For Shape A κ-form, the schedule accounts for only about 3.5% of S₄ (3.20 → 3.09). Per step it shifts by ±(16–40)%, but the dominant part survives the switch to a dyadic schedule.

## Decomposition (Shape A κ-form is a shape effect, not a schedule effect)

The Lean κ-form identification is r_F² = κ(r_C²+ε). On the proxy with Shape A (r_F = λ_{j+1}, r_C = λ_j) and an exact dyadic schedule (λ_{j+1}² = λ_j), this requires

  κ_j(λ_j² + ε_j) ≥ λ_j.

Once the schedule mismatch is gone, the remaining budget is entirely **Φ's quadratic-form defect (ε_j) plus κ_j − 1**. That residual does **not** vanish:

- At κ = 1: ε^A_j = λ_j − λ_j² = λ_j(1−λ_j). This is the price of comparing one fine step (physical time a/2) to one coarse step (time a).
- At ε = 0: κ_j = 1/λ_j = e^{Δ_j}, so κ_j − 1 = e^{Δ_j} − 1.

Since Δ_{j0+k} = Δ_{j0}/2^k, both weighted terms tend to a **constant** instead of going to zero:
2^k(κ−1) = 2^k(e^{Δ_{j0}/2^k}−1) ↓ Δ_{j0}, and 2^k ε^A_κ → Δ_{j0} from below. Both weighted sums therefore **grow linearly in n** and are not summable.

| anchor | Lean S_n of ε^A_κ (n = 1…8) | Lean S_n of κ_j−1 (n = 1…8) | limit term |
|--------|-----------------------------|-----------------------------|-----------:|
| j = 4 | 0.060, 0.437, 1.437, 3.088, 5.218, 7.638, 10.22, 12.89 | 14.69, 20.61, 24.58, 27.86, 30.87, 33.74, 36.55, 39.34 | Δ₄ = 2.753 |
| j = 6 | 0.070, 0.470, 1.468, 3.063, 5.087, 7.368, 9.790, 12.29 | 12.11, 17.35, 20.96, 23.99, 26.78, 29.46, 32.09, 34.69 | Δ₄ = 2.573 |

Project-status form (absolute 2^j weights, a different indexing from Lean S_n):

| anchor | Σ_{j=4..7} 2^j ε^A_κ | Σ_{j=4..11} 2^j ε^A_κ | Σ_{j=4..7} 2^j(κ_j−1) | Σ_{j=4..11} 2^j(κ_j−1) |
|--------|---------------------:|----------------------:|----------------------:|-----------------------:|
| j = 4 | 49.4 | 206.2 | 445.8 | 629.4 |
| j = 6 | 49.0 | 196.6 | 383.9 | 555.0 |

The terms grow (2^j ε → 16Δ₄ per step) instead of decaying. So on the dyadic schedule, **Shape A κ-form still needs nonzero ε or κ > 1, and its 2^j-weighted budget diverges linearly.** This is a **shape** effect: Δ_j ∝ a_j and 2^j a_j = const. It is consistent with the "one-step no-go" recorded in Lean commit 30977c45. Shape B (T_{j+1}² ↔ T_j) carries no such term on this proxy.

## Verdict (lit/MC only, not proof)

On an exact dyadic schedule anchored at afNome j = 4 (or j = 6), the proxy schedule-mismatch ε vanishes to machine precision for Shape B and Shape A κ-free. That removes the whole 398bac67 budget of S₄ ≈ 0.63. The schedule itself stays within about 6% of afNome in 1−w. Shape A κ-form keeps an irreducible one-step-vs-one-coarse residual, λ_j − λ_j² or κ_j − 1 = e^{Δ_j} − 1, whose 2^j-weighted sums grow linearly. So **Shape B is the viable shape** and Shape A's κ-form is not summable on this proxy. This is a shape effect, not a schedule effect. **Lit/MC only, not proof.**

## Bibliography

1. B. Lucini, M. Teper, U. Wenger, JHEP 06 (2004) 012 [hep-lat/0404008], Table 14: SU(2) continuum m_{0⁺⁺}/√σ = 3.78(7).
2. M.J. Teper, hep-th/9812187: SU(2) 3.74 ± 0.12 (cross-check).
3. J. Fingberg, U. Heller, F. Karsch, Nucl. Phys. B 392 (1993) 493 [hep-lat/9208012].
4. S.P. Booth et al. (UKQCD), Nucl. Phys. B 394 (1993) 509 [hep-lat/9209007].
5. Sibling notes: `af_nome_asqrt/AF_NOME_ASQRT_SCHEDULE.md` (a10b9ea4) and `af_nome_eps/AF_NOME_EPS_INTERTWINER.md` (398bac67).
6. Lean: `YMGap/Continuum/BF4WilsonAllNomeRGStepComposition.lean` (`RgRateRelation`, `RgRateRelationκ`, `weightedErrorSum`, `ApproxRgIntertwiner`).

## Files

- `dyadic_schedule_eps.py`: imports the a10b9ea4 interpolation and the 398bac67 ε code
- `dyadic_schedule_anchor_j{4,6}.csv`, `dyadic_eps_anchor_j{4,6}.csv`, `eps_side_by_side_afnome_vs_dyadic.csv`
- `dyadic_schedule_eps_stdout.txt`: full run output
