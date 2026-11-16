# AUDIT: two-loop AF nome schedule (`lean/YMGap/RG/TwoLoopAfSchedule.lean`), 2026-11-15

**Compiled with direct `lean -M 6144` against the overlay** (`/workspace/v3logs/direct_build2.py`,
`LEAN_PATH=/workspace/v3logs/overlay`): rc 0, zero warnings, peak Lean RSS 1,724 MiB, min free RAM
12,886 MiB. Axioms (temp file, deleted): `twoLoopSchedule`, `twoLoop_join`, `twoLoop_steps`,
`twoLoop14_near_afNome12` use `[propext, Quot.sound]`; `tlGap_le_of_modulus` uses `[propext]`.
New file only; no existing statement or proof edited. No sorry/admit/Classical/native_decide/omega/simpa.

U(1) note: the seed witness at w ≤ 1/55 is abelian-valid, so it is not non-abelian evidence.
Any uniform gap at w ≳ 1/8 would NOT hold for U(1) (massless Coulomb phase at matched β; YM
Numerics interim report (numerical, relayed via YM Bot, 2026-11-15), not proved), so it would be
genuine non-abelian content (hcross_OPEN beyond 1/8, AF-regime inputs). Per the numerics, the U(1)
transition lies between 1/8 and 1/2, inside the crossover.

## What is PROVED (Lean)
* `twoLoopSchedule : NomeSchedule`: `0 < w_j < 1`, monotone, and `w_j → 1` with the modulus
  `limitModulus ε = 31 + 1941659·ε.den`. Head `j < 31` by bounded `decide`; tail `j ≥ 31` by the
  closed form `w_j = 1 - 1941659/E_j`, `E_j = 10⁶ j + 1197103 + Σ_{k≤j} ⌊608078/k⌋` (monotone
  because `E_j` is monotone in Nat).
* `twoLoop_join`: `w_0 = 1/64 ≤ 1/55`, `w_j = dyTable j` for `j < 6`, `w_6 = 779/1000`.
* `twoLoop_steps`: `DyadicRGStep w_n w_{n+1}` for every `n < 40`, which covers the crossover, the join
  5→6, the two-loop table, and the table/tail junction 30→31. `DyadicRGStep` is the existing
  definition in `DyadicCrossoverSchedule.lean:47`.
* `twoLoop14_near_afNome12`: `|w_14 − afNome 12| < 10⁻³`.

## What is MOTIVATION only (numerical, python/mpmath 40 digits, not a theorem)
* Coefficients for SU(2), N = 2. Standard convention `μ dg/dμ = −b0 g³ − b1 g⁵`:
  * `b0 = 11N/(48π²) = 0.0464389`;
  * `b1 = (34N²/3)/(16π²)² = 0.00181793`;
  * `κ = b1/(2b0²) = 0.4214876… = 51/121` (exact, matching `afKappa`);
  * `A = 1/(16 b0 ln 2) = 1.941659` (matching `afA = 1942/1000`). `κ/ln 2 = 0.608078`.
* Map from the Numerics README: `w = e^{−t/4}`, `g² = 2t`, `β = 4/g² = 2/t`.
* Two-loop running with `a_j = 2^{−(j−6)} a_6`: `x_j − κ ln(2x_j) = x_6 − κ ln(2x_6) + (j−6) ln 2`,
  where `x = 1/(2 b0 g²)`. It is anchored at `w_6 = 0.779` (the last Numerics-TM-checked point,
  gap 3.198).
* Table `j = 6..30`: `1 − w_j` rounded to 10⁻⁶. The effective two-loop index of each rounded value
  deviates by at most 3·10⁻⁴ per step from 1 (that is, `|log₂(a_j/a_{j+1}) − 1| ≤ 3·10⁻⁴`).
* Tail `j ≥ 31`: the constant 1197103 is fitted to the exact `1 − w_31` (relative error 1·10⁻⁸ there).
  * The relative error in `1 − w` is ≈ 3·10⁻⁴ for `j ≤ 80`.
  * The per-step `|log₂ ratio − 1|` is ≤ 1.14·10⁻³ (largest at j = 31, decreasing to 2·10⁻⁶ by j = 1000).
  * `⌊608078/k⌋` vanishes only for `k > 608078`, after which the surrogate stops tracking `κ log₂ j`.
    It stays monotone and → 1 regardless.
* **Caveats.**
  * `j = 6..8` sits at β ≈ 2.0–2.6, below β = 2.85, where the literature starts trusting two-loop.
    This part of the table extrapolates.
  * `j < 6` is NOT two-loop. It is the dyadic crossover table: steps 0–5 passed the Numerics TM
    check, and each step passes the `DyadicRGStep` test only.
  * Two-loop extrapolated backward from j = 6 breaks down; `x` becomes too small.

## Index consistency and join status
* The schedule is index-consistent with no offset: `scaleChain_crossover_floor` takes a general
  `NomeSchedule`, and `hafδ_OPEN` uses `afGap(j0+n)` and `inv` as a budget function independent of `ns`.
  No existing file needs editing.
* Join with the dyadic crossover from 1/64 is natural, at index 6 (`w_6 = 779/1000 = dyTable 6`).
* Observation: two-loop `w_14 ≈ afNome 12 = 0.8875`. Under two-loop running, the old
  `CrossoverInstance` endpoint is 14 dyadic steps from the seed, not 12.

## Table (j = 0..31)
| j | w_j exact | w_j decimal | two-loop t_j | two-loop g²_j = 2t_j | β=4/g² | source |
|---|---|---|---|---|---|---|
| 0 | 1/64 | 0.015625 | (t(w)=16.6355) | (2t=33.2711) | — | dyadic crossover (not two-loop) |
| 1 | 1/8 | 0.125000 | (t(w)=8.31777) | (2t=16.6355) | — | dyadic crossover (not two-loop) |
| 2 | 7/20 | 0.350000 | (t(w)=4.19929) | (2t=8.39858) | — | dyadic crossover (not two-loop) |
| 3 | 14/25 | 0.560000 | (t(w)=2.31927) | (2t=4.63855) | — | dyadic crossover (not two-loop) |
| 4 | 67/100 | 0.670000 | (t(w)=1.60191) | (2t=3.20382) | — | dyadic crossover (not two-loop) |
| 5 | 147/200 | 0.735000 | (t(w)=1.23154) | (2t=2.46308) | — | dyadic crossover (not two-loop) |
| 6 | 779/1000 | 0.779000000 | 0.99897693 | 1.9979539 | 2.002 | two-loop table |
| 7 | 32123/40000 | 0.803075000 | 0.87722722 | 1.7544544 | 2.2799 | two-loop table |
| 8 | 822281/1000000 | 0.822281000 | 0.78269383 | 1.5653877 | 2.5553 | two-loop table |
| 9 | 418991/500000 | 0.837982000 | 0.70703659 | 1.4140732 | 2.8287 | two-loop table |
| 10 | 851071/1000000 | 0.851071000 | 0.6450385 | 1.290077 | 3.1006 | two-loop table |
| 11 | 10777/12500 | 0.862160000 | 0.59325971 | 1.1865194 | 3.3712 | two-loop table |
| 12 | 871679/1000000 | 0.871679000 | 0.54933559 | 1.0986712 | 3.6408 | two-loop table |
| 13 | 175989/200000 | 0.879945000 | 0.51158457 | 1.0231691 | 3.9094 | two-loop table |
| 14 | 110899/125000 | 0.887192000 | 0.47877676 | 0.95755352 | 4.1773 | two-loop table |
| 15 | 893599/1000000 | 0.893599000 | 0.44999098 | 0.89998197 | 4.4445 | two-loop table |
| 16 | 899307/1000000 | 0.899307000 | 0.42452315 | 0.84904631 | 4.7112 | two-loop table |
| 17 | 36177/40000 | 0.904425000 | 0.40182555 | 0.8036511 | 4.9773 | two-loop table |
| 18 | 11363/12500 | 0.909040000 | 0.38146549 | 0.76293098 | 5.2429 | two-loop table |
| 19 | 114153/125000 | 0.913224000 | 0.36309648 | 0.72619295 | 5.5082 | two-loop table |
| 20 | 183407/200000 | 0.917035000 | 0.34643769 | 0.69287538 | 5.773 | two-loop table |
| 21 | 460261/500000 | 0.920522000 | 0.33125903 | 0.66251806 | 6.0376 | two-loop table |
| 22 | 923723/1000000 | 0.923723000 | 0.31737015 | 0.63474029 | 6.3018 | two-loop table |
| 23 | 463337/500000 | 0.926674000 | 0.30461214 | 0.60922428 | 6.5657 | two-loop table |
| 24 | 929403/1000000 | 0.929403000 | 0.29285133 | 0.58570267 | 6.8294 | two-loop table |
| 25 | 465967/500000 | 0.931934000 | 0.28197441 | 0.56394882 | 7.0928 | two-loop table |
| 26 | 934287/1000000 | 0.934287000 | 0.27188468 | 0.54376937 | 7.3561 | two-loop table |
| 27 | 468241/500000 | 0.936482000 | 0.26249914 | 0.52499828 | 7.6191 | two-loop table |
| 28 | 469267/500000 | 0.938534000 | 0.25374609 | 0.50749218 | 7.8819 | two-loop table |
| 29 | 117557/125000 | 0.940456000 | 0.2455633 | 0.4911266 | 8.1445 | two-loop table |
| 30 | 47113/50000 | 0.942260000 | 0.23789648 | 0.47579296 | 8.407 | two-loop table |
| 31 | 32704311/34645970 | 0.943957147 | 0.23069804 | 0.46139608 | 8.6693 | tail formula |

Lines: 204 (Lean) + this audit.
