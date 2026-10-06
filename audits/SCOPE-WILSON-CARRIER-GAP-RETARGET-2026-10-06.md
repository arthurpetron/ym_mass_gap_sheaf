# Scope note: retarget the gap branch to the Wilson carrier (avoid the bridge)? (2026-10-06 PT)

This is a scope note. Its Lean companion, `BF4WilsonAllNomeExprMixRateContraction.lean`, is
plumbing only. It makes NO progress on the gap input.

## Verdict

**Retargeting is FEASIBLE: the bridge can be avoided. It needs X1–X3 below; the analytic
content sits entirely in X2.**

- **X1 (finite plumbing).** A carrier-parametric, or Wilson, copy of
  `DynamicVacuumSectorCompletedFamily`. Its `completedGap` slot becomes
  `WilsonVacuumSqContraction` at the scale's `(w_j, width_j)`. Re-prove
  `completedAutocorrelation_sq_decay` on Wilson. All ingredients exist:
  `completed_iterated_norm_gap`, `completed_even_lag_corr_decay` and
  `completedInner_cauchySchwarz`. The family is INHABITED unconditionally at
  `rate = mixRate(w_j, width_j) < 1` for every `w_j ∈ (0,1)`. So the cube's `w ≤ 1/2` wall
  does not exist on Wilson.
- **X2 (OPEN analytic; the mass gap).** The band's lower half:
  `m·2^-j ≤ 1 − rate_j`.
  - With the existing rate this reads `m·2^-j ≤ mixFraction_j = kineticFloor/kineticCap`.
    That is a Doeblin floor/cap ratio over the two-slice Haar carrier of `width_j`. It is
    neither shown nor expected to decay only like `2^-j`, so a new quantitative rate producer
    is needed.
  - The upper half is free given the step-ratio input, by compatibility (cf08f0df).
  - The physical meaning of `2^-j` still needs the open AF calibration, as before.
- **X3 (B05 / observable layer).** A Wilson `ObservablePin`: gauge-invariant local
  observables mapped into Wilson `VacuumComplement`, with the norm pin and the amplitude
  bound. Downstream OS/GNS handoffs must also be re-pointed: the selected Wilson GNS datum is
  uninhabited and is not identified with `Completion`. That part is J02-level and open.

## (1) What B04/B05 consumers actually use from the cube carrier

The family `DynamicVacuumSectorCompletedFamily`
(`BF4PhysicalDynamicVacuumSectorCompletedFamily.lean:53`) has the fields nome, spacing, and
`completedGap : CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData`.

| Use | Where | Property used |
|---|---|---|
| `latticeMargin`, `physicalGap`, `DynamicVacuumSectorPhysicalRateBand` (B04 band) and its compilers (`…WilsonExactRateHandoff` uses only `family.physicalGap`) | `…CompletedFamily.lean:67,73,121` | SCALARS ONLY: `rate`, `rate_nonnegative`, `rate_lt_one`, `spacing` |
| `completedAutocorrelation_sq_decay` | `…CompletedFamily.lean:88` → `centralPhysical…Autocorrelation_sq_decay` (`BF4PhysicalCutoffVacuumSectorCylinderCompletedGap.lean:245`) | the ALL-VECTOR `contraction`, the completed inner product, the transfer and its powers, Cauchy–Schwarz |
| `DynamicVacuumSectorSameObjectRCChannel` and its decay; `ScheduledRCChannel` sampling | `…SameObjectRCChannel.lean:56,139`; `…ScheduledRCChannel.lean:101` | the contraction applied to ONE vector per scale (`vectorAt scale`) |
| `connectedAutocorrelation_eq_global` | `…SameObjectRCChannel.lean:157` | the cube sector's embedding in the global cutoff completion (cube-specific; feeds the GNS handoffs) |
| `DynamicVacuumSectorObservablePin`, `connectedCorrSq_le_rateSq_normFourth` (the B05-shaped every-observable decay) | `…ObservablePath.lean:74,130` | the contraction applied to `vectorAt scale O` for EVERY observable `O` |
| `toPhysicalSeparator` | `…ObservablePath.lean:216` | the scalar `rate` |

No consumer uses the conditional Markov structure or extent one. The family is generic in
`half`. Those enter only the PRODUCER `completedSectorContraction`
(`BF4PhysicalCubeCompletedMarginalGap.lean:58`, through the Markov-form Cauchy–Schwarz data
and the `w ≤ 1/2` Gaussian tail).

## (2) What the Wilson carrier already provides

| Needed | Wilson Lean | Status |
|---|---|---|
| Completed inner product, Cauchy–Schwarz | `completedInner`, `completedInner_cauchySchwarz` (`BF4WilsonAllNomeCompletedInner.lean:64,82`) | present |
| Transfer and powers, self-adjoint | `completedTime`, `completedTime_add`, `completedInner_time_balance` (`BF4WilsonAllNomeCompletedTime.lean`) | present |
| Vacuum sector | `VacuumComplement` with `B U x = 0`, time-invariant (`…CompletedTime.lean:171,173`) | present |
| **All-vector strict squared-norm contraction** | `completed_oneStep_norm_gap` (`BF4WilsonAllNomeCompletedGap.lean:200`): `B(T^(n+1)x,T^(n+1)x) ≤ mixRate²·B(T^n x,T^n x)` for every `x ⊥ U`, for ALL `0<w<1` and every width. Also `completed_iterated_norm_gap` and `completed_even_lag_corr_decay` (`:214,234`) | present; restated as `WilsonVacuumSqContraction` / `wilsonVacuumSqContraction_mixRate` (this pass) |
| Orbit contraction of the Expr anchor | `expr_orbitContraction_mixRate` (this pass) | present, UNCONDITIONAL, at rate `mixRate` |
| Rayleigh form | `WilsonVacuumRayleighRate` (`BF4WilsonAllNomeH1FixedScale.lean:476`) | OPEN for `r<1`, and not needed (see 4) |
| Quantitative band `m·2^-j ≤ 1−rate_j` | `mixRate = 1 − mixFraction` (`BF4ExactSlabFixedSpatialTransferMixingRate.lean:81,110`) | MISSING (X2) |
| Dynamic-family record and observable pin on Wilson | none | MISSING (X1 plumbing, X3) |

## (3) Wilson statements and the `w ≤ 1/2` producer

- **Wilson B04 band.** Given a nome schedule `w_j`, widths `width_j` and per-scale
  `r_j` with `WilsonVacuumSqContraction (w_j) (width_j) r_j`, require
  `∃ m M > 0, ∀ j, m·2^-j ≤ 1 − r_j ≤ M·2^-j`.
  - On the Expr layer, `ExprPhysicalRateBand` (cf08f0df) is exactly this shape for the anchor
    rate.
  - `exprCenteredContractionLower_mixRate` shows that at `r_j = mixRate_j` the ONLY open
    field is the lower margin.
- **Wilson B05.** For every gauge-invariant local `O`, with `v_j(O) ∈ VacuumComplement`:
  `B(v, T^n v)² ≤ (r_j²)^n · ‖v‖⁴`, plus the physical-time sampling `n = ⌊t/a_j⌋`.
  - This follows from `WilsonVacuumSqContraction`, Cauchy–Schwarz and `completedTime_add`
    (finite, X1).
  - The every-`O` uniformity in `j` needs X2 and X3.
- **The cube producer is not portable, and not needed.** It is built on the cube Markov form
  and its Gaussian return tail, with `w ≤ 1/2` entering only there. Wilson already has its
  own all-nome strict contraction, with no `w` restriction. The blocker is quantitative, not
  existence.

## (4) Orbit vs all-vector

- **Single-channel consumers** (`SameObjectRCChannel`, `ScheduledRCChannel`, continuum
  zero-time positivity) apply the contraction only to their one channel vector. An orbit
  contraction on that vector, e.g. the centered anchor, SUFFICES.
- **B05** (`ObservablePin`: every observable `O`, "EVERY-state decay") GENUINELY needs the
  rate on every observable vector, i.e. all-vector. The anchor orbit alone is not enough.
- **Directions.**
  - All-vector ⇒ orbit is trivial; proved as `orbitContraction_of_vacuumSq`.
  - Orbit ⇒ all-vector is false in general.
- **Rayleigh vs squared norm.** `WilsonVacuumRayleighRate r` (`B(y,Ty) ≤ r B(y,y)`) is all-vector,
  but in the T-form. B05 consumes the T²-form `B(Ty,Ty) ≤ r² B(y,y)`.
  - Finite route: Rayleigh at `y` and `Ty` (time-invariance), together with
    `response_log_convex_step` (`BF4WilsonAllNomeOddResponseJensen.lean:222`), gives
    `R(2)² ≤ r² R(0) R(2)`. It remains to cancel `R(2) ≥ 0`.
  - The cancellation `0≤a, 0≤b, a·a ≤ b·a ⇒ a ≤ b` is constructively true for the eventual
    order `leEv` (`CRealComplete.lean:94`), but it needs an approximation-level proof that
    handles the `RCmul` representative. I estimate about 100 lines; it is not in the repo, so
    I did not do it.
  - It is UNNECESSARY for the retarget: the existing Wilson rate is already in the T²-form.

## Lean added (plumbing)

`BF4WilsonAllNomeExprMixRateContraction.lean`:
- `WilsonVacuumSqContraction`;
- `wilsonVacuumSqContraction_mixRate`;
- `orbitContraction_of_vacuumSq`;
- `expr_orbitContraction_mixRate`;
- `exprCenteredContractionLower_mixRate`.

All are `[propext, Quot.sound]`.

## X1 done: `BF4WilsonAllNomeWilsonDynamicFamily.lean` (PLUMBING; 2026-10-06 PT)

This is additive; no cube-side file was touched. It makes NO progress on X2 or on the
step-ratio input.

What the module provides:
- **`WilsonDynamicFamily`.** A mirror of the cube `DynamicVacuumSectorCompletedFamily`. The
  cube `…StrictContractionData` slot is replaced by `rate`, `rate_nonnegative`,
  `rate_lt_one`, and `contraction : WilsonVacuumSqContraction` (all-vector, Wilson carrier of
  width `width j`).
- **Margin and gap.** `latticeMargin`, `physicalGap`, `latticeMargin_pos`.
- **Decay, re-proved on Wilson.** `completedAutocorrelation_sq_decay`, in the cube's exact
  shape: `B(y,Tⁿy)² ≤ ((r·r)ⁿ B(y,y))·B(y,y)` on `VacuumComplement`. The proof uses
  `iterated_of_vacuumSq` (the generic-rate analogue of `completed_iterated_norm_gap`), then
  Cauchy–Schwarz.
- **Family on the trajectory.** `exprWilsonFamily tr r …` lives on the SAME schedule and
  widths as the Expr trajectory, with spacing `2^-j`. `exprMixRateFamily tr` is
  unconditional, at `mixRate(w_j, width_j)`.
- **Band as a Prop.** `WilsonPhysicalRateBand F := ∃ m M, WilsonLowerMargin F m ∧
  WilsonUpperMargin F M`. Here `WilsonLowerMargin F m` is X2.
- **Upper half without X2.** `wilsonUpper_of_stepRatio` derives the upper half from the
  step ratio alone, via the cf08f0df compatibility.
- **Capstone.** `wilsonGapBranch_of_stepRatio_lowerMargin` (any family on `tr`) and
  `wilsonGapBranch_mixRate`.
  - Open hypotheses:
    - H-var, H-ray, and the step ratio (`ExprStepRatio`, `hc`, ranges of `ρ'`). These are
      the 9d58a5df nontriviality bundle.
    - X2.
  - Everything else is an arithmetic parameter choice.
  - Conclusions: A03, `WilsonPhysicalRateBand`, decay at every scale and every
    vacuum-complement vector, and `m ≤ 2^(2C+3)`.

Honest status:
- On the gap side, X2 is the single open input.
- The goal of "exactly one open analytic input" overall is NOT met. The nontriviality bundle
  (H-var + H-ray + step ratio) is also open; it sits on the same carrier and trajectory.
- At `mixRate`, X2 means `m·2^-j ≤ mixFraction_j`, which is not expected to hold. A sharper
  Wilson rate producer may be needed; the generic capstone accepts any family.
- **X3 TODO (J02-level).** A Wilson `ObservablePin`, OS/GNS re-pointing, and AF calibration.

## Instance on the AF-padded `Y_j` trajectory (`BF4WilsonAllNomeWilsonGapBranchAFPadded.lean`)

This section records an instantiation; it is plumbing only.

`wilsonGapBranch_afPadded` instantiates `wilsonGapBranch_mixRate` on the following data:
- **Trajectory.** `afPaddedZeroMomentumAFExpr.toExprAnchorTrajectory`, which is
  `afPaddedZeroMomentumExpr` by `rfl`.
- **Rate family.** `exprMixRateFamily` of that same trajectory.
- **H-var.** Discharged by `afPaddedZeroMomentumExpr_hvar`, i.e. `toExpr_hvar`, with
  `v = paddedVar`.
- **H-ray.** Discharged by `afPaddedZeroMomentumExpr_hray`, i.e. `toExpr_hray` with
  `afPaddedZeroMomentum_padded`, with `ρ = paddedRho`.

Open analytic hypotheses (exactly two):
1. `ExprStepRatio`, with `side_j(1−ρ'_j) ≤ c` for `j ≥ j0` and ranges for `ρ'`;
2. `WilsonLowerMargin (exprMixRateFamily _) m` (X2).

Everything else is arithmetic: `ha hC hcC hj0 hj0' hdelta0 hdelta hcd hk`.

Conclusions:
- `ExprAFCalibrated _ afA afKappa afC` (two-loop shape only);
- A03;
- `WilsonPhysicalRateBand`;
- `WilsonFamilyDecay`;
- `m ≤ 2^(2C+3)`.

All axioms are `{propext, Quot.sound}`.
