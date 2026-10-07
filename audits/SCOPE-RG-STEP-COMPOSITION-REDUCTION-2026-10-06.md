# RG-step composition reduction for the Wilson gap frontier (2026-10-06 PT)

Status: **REDUCTION ONLY.** No approximate intertwiner `Φ_j` is constructed.
Operator-level `ApproxRgIntertwiner` fields + proved rate transfer; SC cannot seed `trAF`.
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

together with errors `ε_j ≥ 0` and coercivity constants `κ_j > 0`, such that:

1. **Coercive lower bound** (prevents `Φ = 0`): `B_{j+1}(x,x) ≤ κ_j · B_j(Φx, Φx)`.
   (The older "nonexpansive" upper bound `B_j(Φx,Φx) ≤ B_{j+1}(x,x)` alone
   allowed the zero map and is **not** sufficient.)
2. **Norm upper bound**: `B_j(Φx, Φx) ≤ B_{j+1}(x,x)`.
3. **Approx intertwining (quadratic-form defect):** a one-step VacSq B-form
   `B_{j+1}(T_{j+1} x, T_{j+1} x) ≤ κ_j·B_j(T_j Φx, T_j Φx) + (κ_j·ε_j)·B_{j+1}(x,x)`
   (constructive packaging of `Φ∘T² ≈ T∘Φ` without vector subtraction on the
   subtype; see Lean).
4. **Rate transfer (PROVED from 1–3):** coarse VacSq at `r_j` implies fine
   square-factor `κ_j(r_j²+ε_j)`, hence VacSq at any `r_{j+1}` with
   `κ_j(r_j²+ε_j) ≤ r_{j+1}²`. Choosing equality identifies
   `r_{j+1}² = κ_j(r_j²+ε_j)`.

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
  guards (`heatRatio ≤ 1/2`, `heatRemainderBound < 1`, entropy-rate).
* **Verdict on `trAF` / `afNomeSchedule`:** every scale fails the first guard.
  Proved: `afGap 0 < 1/2`, so `w_0 > 1/2`; by `nome_mono`, `w_j ≥ w_0` for all
  `j`; hence `heatRatio(w_j) ≥ heatRatio(1/2) = 4 > 1/2`
  (`not_heatRatio_le_half_afNome`). Strong coupling **cannot** seed `trAF`.
* The seed for the RG reduction on `trAF` is therefore an **open
  intermediate-coupling** contraction producer (neither SC nor a completed
  weak-coupling/AF producer).
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
   * a seed contraction at some `j0` (SC cannot seed `trAF`; need an open
     intermediate-coupling producer), and
   * approx RG intertwiners with `Σ 2^j ε_j` small enough to leave a positive
     dyadic lower margin.

No new analytic estimate is claimed. Exact missing input: quantitative
construction of `Φ_j` (or direct verification of the rate-transfer Prop) with
summable `ε_j` for the Wilson action along the chosen schedule.
