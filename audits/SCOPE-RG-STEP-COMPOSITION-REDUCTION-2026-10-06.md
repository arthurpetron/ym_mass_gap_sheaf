# RG-step composition reduction for the Wilson gap frontier (2026-10-06 PT)

Status: **REDUCTION ONLY.** No approximate intertwiner `Φ_j` is constructed.
Companion Lean: `lean/YMGap/Continuum/BF4WilsonAllNomeRGStepComposition.lean`.

## Question

Can the gap frontier on `trAF` (`WilsonAFPaddedGapInput`: a rate family with
`WilsonVacuumSqContraction` at each `(w_j, width_j)` and a dyadic lower margin
`m·2^{-j} ≤ 1 − r_j`) be restated as:

1. the existing open step-ratio input, and
2. inhabitability of approximate RG intertwiners `Φ_j` with summable weighted
   errors `Σ 2^j ε_j`, seeded by a known contraction at some coarse scale `j0`?

## Width / scale schedule (honest)

* YM Bot's sketch used width `2^j`. The live AF-padded trajectory `trAF` uses
  `width_j = trajWidth j = 4^j + 1` and physical spacing `a_j = 2^{-j}`
  (`BF4DyadicWilsonSquare.spacing`). These are **not** the same.
* The reduction below is **abstract in the scale index `j`**: it applies to any
  family with consecutive scales `(j+1) → j`, nomes `w_j`, widths `width_j`, and
  transfers `T_j = completedTime` on
  `BF4WilsonAllNomeCompletedInner.Completion (w_j) (width_j)`.
* Mapping to `trAF`: take the actual `(w_j, width_j)` of `trAF`. The factor-two
  intertwining `T_{j+1}² ↔ T_j` matches the dyadic spacing ratio
  `a_{j+1} = a_j / 2` (two fine lattice time steps ≈ one coarse physical step).
  The width jump `4^j+1 → 4^{j+1}+1` is **not** a spatial 2-blocking; any real
  `Φ_j` must account for that. The rate algebra does not care.

## Per-scale hypothesis (what would have to be inhabited)

At each `j`, an **approximate RG intertwiner**

```
Φ_j : VacuumComplement (w_{j+1}) (width_{j+1}) → VacuumComplement (w_j) (width_j)
```

together with an error `ε_j ≥ 0`, such that:

1. **Nonexpansive** (or isometric): `B_j(Φ x, Φ x) ≤ B_{j+1}(x, x)`.
2. **Approx intertwining**: `Φ ∘ T_{j+1}²` is within `ε_j` of `T_j ∘ Φ` in the
   completed vacuum-complement norm (precise B-form in the Lean module's
   documentation; the rate-level shadow is what the reduction consumes).
3. **Rate transfer (REDUCTION input):** if the coarse scale contracts at rate
   `r_j` (`WilsonVacuumSqContraction … width_j r_j`), then the fine scale
   contracts at any `r_{j+1} ≥ 0` with
   `r_{j+1}² ≤ r_j + ε_j` (and `r_{j+1} < 1`).

Exact intertwiners (`ε_j = 0` with literal `Φ T² = T Φ`) almost certainly do
**not** exist for the Wilson action: different widths, different nomes `w_j`, no
exact blocking identity for continuum YM, and the AF width schedule is not a
pure 2-blocking. Any honest `ε_j` must come from quantitative RG / polymer /
continuum-limit estimates (Balaban-style or modern constructive QFT). **That
input is not supplied here.**

## Rate algebra (proved, pure Q')

From `0 ≤ rFine ≤ 1` and `rFine² ≤ rCoarse + ε ≤ 1`:

* `1 − rFine ≥ (1 − rFine²)/2 ≥ (1 − rCoarse − ε)/2`.

So each RG step at least halves the available lattice margin, minus an
`ε`-penalty. Unfolding from a seed `r_{j0}` with partial weighted sums
`S_n = Σ_{k<n} 2^k ε_{j0+k}` bounded by some `S < 1 − r_{j0}` yields

* `1 − r_{j0+n} ≥ 2^{-n} (1 − r_{j0} − S)` (up to the precise indexing in Lean),

hence a dyadic lower margin `m · 2^{-j} ≤ 1 − r_j` with
`m ∼ (1 − r_{j0} − S) · 2^{j0}`. This is exactly the shape of
`WilsonLowerMargin` on `dyadicPhysicalSpacing`.

## Seeding by strong coupling (honest limits)

* `allNome_strongCoupling_vacuumSq` gives `WilsonVacuumSqContraction` at
  `timeRate = 1/4` for **every** literal width, under the three small-nome
  guards.
* Every `NomeSchedule` (including `trAF`) has `w_j → 1` and **leaves** the
  strong-coupling window. The SC seed can be used only at scales `j0` that
  still satisfy the guards. If no such `j0` exists on `trAF`, SC does not
  seed that trajectory; the reduction still applies to any other seed
  (e.g. a future weak-coupling / AF producer at large `j`).
* A constant rate still fails the B04 upper half
  (`constant_rate_not_all_scale_upper`). The composed family has rates that
  may rise toward 1 as `ε`-errors accumulate; the upper half remains the
  separate step-ratio input.

## What this does / does not do

| Does | Does not |
|---|---|
| Restate part of the gap frontier as inhabitability of `Φ_j` / `ε_j` | Construct any `Φ_j` |
| Prove the rate/margin algebra | Progress on Balaban-style estimates |
| Give a conditional path to `WilsonAFPaddedGapInput` | Discharge `WilsonAFPaddedGapInput` |
| Keep SC and AF labels honest | Feed SC rates into the AF capstone unconditionally |

## Restated frontier (REDUCTION)

On `trAF`, `wilsonGapBranch_afPadded_generic` still needs:

1. **Step ratio** (`ExprStepRatio`) — unchanged, open.
2. **`WilsonAFPaddedGapInput`**, which along this route splits as:
   * a seed contraction at some `j0` (SC only if `w_{j0}` is still guarded;
     otherwise a different producer), and
   * approx RG intertwiners with `Σ 2^j ε_j` small enough to leave a positive
     dyadic lower margin.

No new analytic estimate is claimed. Exact missing input: quantitative
construction of `Φ_j` (or direct verification of the rate-transfer Prop) with
summable `ε_j` for the Wilson action along the chosen schedule.
