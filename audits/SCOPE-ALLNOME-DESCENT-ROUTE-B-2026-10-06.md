# Route (b): Descent-style connected decay on the literal all-nome carrier (2026-10-06 PT)

Status: **PROVED (finite adaptation), STRONG-COUPLING ONLY, NOT AF.**
Module: `lean/YMGap/Continuum/BF4WilsonAllNomeStrongCouplingUniformRate.lean`.
Follows route (b) of `SCOPE-UNION-ALLNOME-CARRIER-BRIDGE-2026-10-06.md`.

## Question

Can the Descent connected-decay argument be run directly on
`BF4WilsonAllNomeCompletedInner.Completion hw0 hw1 width` with its `completedTime`
(completion of `advance`), under the three guards (`heatRatio w ≤ 1/2`,
`heatRemainderBound w < 1`, `entropyRate 625 (adjustedCoreRate w hd) < 1`), to inhabit
`WilsonVacuumSqContraction hw0 hw1 width r` at a width-INDEPENDENT `r`?

## Trace of the Descent chain

| Descent step | Union/Stage-specific? | All-nome counterpart |
|---|---|---|
| `finite_covariance_distance_bound` (`BF4ExactSlabDescentSelectedCovariance`) | **No.** Holds for any extent, any nodup physical id list, and any two link-local probes with connected carriers | reused verbatim |
| `connectedScalar_selected_pin` / `chartInsertion_separated` | geometry at spatial collar `r+1` on `chartExtent` | `litInsertion_separated`, `litInsertion_left/right_unit` at spatial offset `0` on `litExtent width H t = width+(t+(2H+t))`. This is literally the extent of `originalWindowScalar`, so the finite scalar pins by `rfl` |
| `upper/lowerProbe_interval`, `_local` | collar recentering | `litUpper/Lower_interval` (`placed_interval`) and `litUpper/Lower_local` (`placed_recenter_local` at `space := 0` plus `includeExpression_placed`) |
| `budget_pin` | none (root distance = lag) | the same proof at spatial shift `0` |
| `connectedScalar_time_converges` (3-regulator diagonal, spatial limit) | **yes**: the guarded form is a spatial limit | replaced by the 2-regulator `originalJoint_diagonal_converges` at the literal width (template: `BF4WilsonAllNomeSeparatedCovariance.intrinsic_centered_covariance_le`) |
| `evenMoment_le_geometric` → `dyadic_geometric_first_le` | none | reused with `BF4WilsonAllNomeCenteredMoments.evenMoment_{nonnegative,le_zero,dyadic}` |
| `representative_twoStep_form_gap` → `oneStep_norm_gap` | carrier plumbing | reused from the rate-independent parts of `BF4WilsonAllNomeCompletedGap` |

Verdict: **finite adaptation.** No new analytic estimate is needed. The one analytic input,
the selected-chain cluster bound, already holds with no spatial collar. The Stage, union,
growing-base and spatial-limit structure only matters for the guarded infinite-volume
form, and route (b) never uses that form.

## What is proved (all under the three guards; axioms ⊆ {propext, Quot.sound})

- `originalWindowScalar_connected_sc_bound`: the finite connected original-window scalar
  at literal width, at every cutoff and boundary depth, satisfies
  `|·| ≤ decayAmplitude w hd width R x y · timeRate^(R+n+1−sizeLoss width R)`.
- `intrinsic_centered_sc_bound`: the same bound for the literal-width all-nome
  intrinsic centered pairing. The proof passes through the witnessed joint limits.
- `sc_centered_twoStep_bound`: a prefactor-free dense estimate,
  `centeredTimeMoment 2 x x ≤ twoStepRate · centeredTimeMoment 0 x x`.
- `sc_oneStep_norm_gap`: on the completion, `B x U = 0 ⇒ B(T1x,T1x) ≤ twoStepRate · B(x,x)`.
- **`allNome_strongCoupling_vacuumSq`**: `WilsonVacuumSqContraction hw0 hw1 width timeRate`.
  `allNome_strongCoupling_vacuumSq_all_widths` states it for all `width` with ONE rate.
- **Non-vacuity** (`existingNome_allNome_strongCoupling`): at `w = 1/1024` all three guards
  are discharged with no free hypotheses (`existingNome_guards`, `existingNome_entropyRate`).
  Then `0 < timeRate < 1` and `∀ width, WilsonVacuumSqContraction … width timeRate`.

Here `timeRate = entropyRate 96 (1/384) = 1/4` and `twoStepRate = timeRate² = 1/16`.

## Why the Doeblin `mixRate` loses `(1/32)^width` and this route does not

`wilsonVacuumSqContraction_mixRate` comes from a transfer-matrix minorization of the
whole width-`width` time slice. The minorization fraction is
`mixFraction ≤ (1/32)^width` (`mixFraction_le_width_power`), so `mixRate → 1` as the
width grows. The cluster route bounds each correlator by connected polymers joining
two probe boxes. The decay per unit time is the entropy-adjusted activity
`timeRate`, which does not depend on volume. The width only enters through the probe
box (`probeBoxSize width R = max(width+1, R+1)`), and so through `sizeLoss` and
`decayAmplitude`. The dyadic spectral step (`dyadic_geometric_first_le`) removes that
amplitude completely.

## Honest limits

- **Strong coupling only.** The guards confine `w` to a small-nome window. Every
  `NomeSchedule` has `w_j → 1` and leaves it.
- **Not AF; does not feed the AF capstone.** A constant rate fails the B04 upper half on
  unbounded `side_j` (`BF4WilsonStrongCouplingUniformRate.constant_rate_not_all_scale_upper`).
- The result is a fixed-width discrete contraction on each literal-width carrier,
  uniform across widths. No cross-width carrier map, spatial limit, continuum,
  Hamiltonian or physical-spacing identification is made. It does not identify the
  all-nome carrier with `UnionCompletion`; the bridge verdict stands.
