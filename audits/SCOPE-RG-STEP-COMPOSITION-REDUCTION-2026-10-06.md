# RG-step composition reduction for the Wilson gap frontier (2026-10-06 PT)

Status: **REDUCTION ONLY.** No approximate intertwiner `Φ_j` is constructed.
Two-step intertwining (`T_f²` vs `T_c`) + proved transfer `r_F⁴ ≤ κ(r_C²+ε)`;
κ≥1 on pinned vacuum diagonals; one-step shape no-go; SC cannot seed `trAF`.
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
   Together with the upper bound ⇒ `κ_j ≥ 1` on any fine vacuum vector whose
   diagonal is pinned to a positive rational `δ` (`kappa_ge_one`).
2. **Norm upper bound**: `B_j(Φx, Φx) ≤ B_{j+1}(x,x)`.
3. **Approx intertwining (two fine steps vs one coarse; B-form):**
   `B_{j+1}(T_{j+1}² x) ≤ κ_j·B_j(T_j Φx) + (κ_j·ε_j)·B_{j+1}(x)`
   (`intertwine_twoStep`; constructive packaging of `Φ∘T² ≈ T∘Φ` without
   subtype subtraction). Matches the dyadic spacing ratio `a_{j+1}=a_j/2`.
4. **Rate transfer (PROVED from 1–3):** coarse VacSq at `r_j` ⇒ fine **two-step**
   factor `α = κ_j(r_j²+ε_j)`. Dictionary: VacSq at `r_F` ⇒ two-step factor
   `r_F⁴` (`vacuumSq_implies_twoStepFactor`), so choosing `r_F⁴ = α` gives
   `r_F⁴ ≤ κ(r_C²+ε)`. Writing `u_j = r_j²` recovers the 8a341453 shape
   `u_{j+1} ≤ u_j + ε'_j` after absorbing `(κ−1)·r_C²` into the effective
   defect `ε' = (κ−1)·r_C² + κ·ε` (`effectiveRgDefect`).

**No-go on the old one-step shape.** If a fine vector attains Rayleigh
`B(Tx)/B(x) ≥ r_C` (pinned diagonal), any one-step defect of the form
`B(Tx) ≤ κ·B(T Φx) + (κ·ε)·B(x)` plus coarse VacSq + upper forces
`r_C ≤ κ(r_C²+ε)`. When `r_C/κ > r_C²`, this lower-bounds `ε`; persistent
attainders along AF prevent `Σ 2^j ε_j` from staying small
(`oneStep_defect_forces_rate_le_kappa_factor`, `OneStepAfSumObstruction`).
This motivates the two-step retype.

Exact intertwiners (`ε_j = 0` with literal `Φ T² = T Φ`) almost certainly do
**not** exist for the Wilson action: different widths, different nomes `w_j`, no
exact blocking identity for continuum YM, and the AF width schedule is not a
pure 2-blocking. Any honest `ε_j` must come from quantitative RG / polymer /
continuum-limit estimates (Balaban-style or modern constructive QFT). **That
input is not supplied here.** Inhabitability of `Φ_j` remains **OPEN**.

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

## Envelope PROVED from the κ chain (2026-10-06 ~9:35 PM PT; REDUCTION)

The old `RgMarginEnvelope` *assumed* its `∀ n` dyadic conjunct. It is now
**derived** (`rgKappa_dyadic_envelope`, `rgMarginEnvelopeκ_dyadic`) from three
hypotheses packaged in `RgMarginEnvelopeκ r ε κ j0 S U`:

1. `RgRateChainκ r ε κ j0` (two-step κ rate relation at each `j ≥ j0`);
2. `RgErrorSummable (effectiveDefectSeq κ ε r) j0 S`: `Σ_{k<n} 2^k eff_{j0+k} ≤ S`
   for every finite `n` (constructive partial sums), `eff_j = (κ_j−1)r_j² + κ_jε_j`;
3. relative upper margin `m_{j0+n} ≤ U·2^{-n}` (the B04 upper half; absolute
   `m_j ≤ M·2^{-j}` gives `U = M·2^{-j0}`).

Step actually used (`margin_after_rg_step_κ`, rewritten with `m = 1 − r`):
`m_{j+1} ≥ m_j/2 − (m_j² + eff_j)/4` — matches YM Bot's form exactly.
Scaled `a_n = 2^n m_{j0+n}`: `a_{n+1} ≥ a_n − U²·2^{-(n+1)} − ½·2^n eff_{j0+n}`
(`rgKappa_scaled_step`; the `m²` term is bounded using the upper margin, so the
B04 upper half is genuinely used). Telescoped (`rgKappa_envelope_invariant`):

* **Sharp:** `2^n·m_{j0+n} ≥ m_{j0} − U² − S/2`, i.e.
  `2^n·m_{j0+n} ≥ m_{j0} − M²·4^{-j0} − S/2`.
* **c = 1 form** (`rgKappa_dyadic_envelope_abs`): `2^n·m_{j0+n} ≥ m_{j0} − (M² + S)`.
* Half-power form: `2^{-n}(m_{j0} − U² − S/2) ≤ m_{j0+n}`.

**Non-vacuity condition.** Useful only if `m_{j0} > U² + S/2` (j0 = 0: `m_0 > M² + S/2`).
Since the upper margin at `n = 0` gives `m_{j0} ≤ U`, this requires `U² < U`, i.e.
`U = M·2^{-j0} < 1`, so one must start at `j0 > log₂ M`; and the seed margin must
dominate `M²·4^{-j0} + S/2`. For the existing `exprWilsonFamily` upper margin
`M = 2^{2C+3} + 2^{j0+2}` the j0 = 0 seed is vacuous; a later start scale is needed.

**Rewired.** `rg_envelope_zero_lower_margin` and `rg_envelope_zero_wilsonLowerMargin`
now take `RgRateChainκ F.rate ε κ 0`, summable effective defect `S`, and
`WilsonUpperMargin F M`, and give the lower margin with seed
`rgSeedMarginκ = m_0 − M² − S/2` (positivity hypothesis). The assumed-envelope
version survives as `rg_envelope_zero_lower_margin_assumed` (legacy).
`exprWilsonFamily_lowerMargin_of_kappaChain` discharges the spacing by `rfl`.

**Spacing verdict.** The envelope uses `spacing j = half^j`. `exprWilsonFamily`,
`exprMixRateFamily` and `trajectoryDynamicFamily` (hence the `trAF` family) use
`dyadicPhysicalSpacing`, with `spacing j = half^j` **by definition**
(`exprWilsonFamily_spacing_half_pow := rfl`) — consistent. `afNomeSchedule`
(`1 − w_j = A/(j + κ⌊log₂(j+1)⌋ + 4)`, `A = 1/(16 b₀ ln 2)`) is calibrated with one
`j`-step = one halving of the spacing, so its scale relation also matches the
factor-2 RG step. Remaining mismatch (documented, not fixed): the widths
`4^j + 1` grow ×4 per step (not a spatial 2-blocking), and there is no concrete
`a(w)` (`NomeSchedulePhysicalBox` open), so the dyadic identification of the nome
schedule with the RG step is a calibration choice, not a theorem.

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

## Changelog

* 2026-10-06 ~8:40 PM PT — Retype to `intertwine_twoStep` (`T_f²` vs `T_c`);
  prove `approxRg_transfers_twoStep_factor` (`r_F⁴ ≤ κ(r_C²+ε)` dictionary);
  `kappa_ge_one`; `effectiveRgDefect = (κ−1)r_C² + κ·ε` in margin budget;
  one-step no-go `oneStep_defect_forces_rate_le_kappa_factor`. Still REDUCTION;
  `Φ` inhabitability OPEN. Axioms ⊆ {propext, Quot.sound}.
* 2026-10-06 ~9:35 PM PT — Envelope PROVED from `RgRateChainκ` + summable
  `eff` + B04 upper half (`rgKappa_dyadic_envelope`, sharp
  `2^n m_{j0+n} ≥ m_{j0} − U² − S/2`; c = 1 form with `M²+S`); zero-scale lower
  margin rewired through κ chain; spacing verdict recorded. REDUCTION; Φ OPEN.
