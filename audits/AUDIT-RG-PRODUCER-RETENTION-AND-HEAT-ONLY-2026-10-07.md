# Actual slow-state retention and heat-only marginal screen (2026-10-07)

Whole-project goal unchanged and OPEN: constructive nontrivial continuum
Yang--Mills on R^4 for every compact simple group, SAME-theory QFT axioms and
a positive physical Hamiltonian mass gap. Continuation of `067111e2`.

## Necessary compatibility of the two current proof fronts

`lean/YMGap/Continuum/BF4WilsonAllNomeRGSlowStateRetention.lean:126`,
`shiftedState`, constructs the actual original box-smoothed excitation
advanced by side_j/2 on its own completed Wilson carrier. Let
A=||x||_fine^2, F=||T_fine^2 x||_fine^2, B=||Phi x||_coarse^2 and
C=||T_coarse Phi x||_coarse^2. The squared time-two norm has response lag
FOUR, not two.

- Same file `:143`, `shiftedState_fourStep_loss`, derives
  `side_j*(A-F) <= 4*c0*A` from the EXISTING shifted H1 input. The private
  finite telescope uses `lean/YMGap/Continuum/BF4WilsonAllNomeTimeDefectMoments.lean:349`,
  `mixedMoment_split`, and
  `lean/YMGap/Continuum/BF4WilsonAllNomeShiftedWindowSurvival.lean:211`,
  `window_energy_antitone`. The four-step loss is not an additional premise.
- `lean/YMGap/Continuum/BF4WilsonAllNomeRGSlowStateRetention.lean:167`,
  `shiftedState_retention`, uses the supplied relative comparison
  `F <= delta*A+(1-delta)*C` and existing coarse time nonexpansiveness to
  prove `side_j*(1-delta)*(A-B) <= 4*c0*A`. No coarse gap is assumed.
- Same file `:182`, `shiftedState_retention_of_cap`, replaces delta by a cap
  D using the supplied upper comparison B<=A. `:217`,
  `shiftedState_retention_of_prefix`, derives delta_n<=D from the ordinary
  nonnegative prefix budget, at fine scale n+1. Both give the cleared bound
  `side_j*(1-D)*(A-B) <= 4*c0*A`, with D<=1.
- Same file `:198`, `shiftedState_retention_of_window`, applies the existing
  `lean/YMGap/Continuum/BF4WilsonAllNomeExprAnchorTrajectory.lean:328`,
  `exprShiftedEpsBound_of_windowSurvival`, retaining its theta/c0 sign guards.

For a positive-norm state and D<1 this means a loss fraction at most
`4*c0/(side_j*(1-D))`. The formal statement divides neither by that norm nor
by 1-D; zero-norm cases stay valid. This is selective retention on ONE
actual slow state, not a full lower norm bound or a prohibition on fringe
erasure. AF window survival and an actual comparison map are still OPEN.

## Exact original action detects the discarded spatial factor

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCubeHeatOnlyObstruction.lean:73`,
`kineticMap_one_haar`, proves the original FREE kinetic map sends one to one
as a supported-Haar tested functional, at EVERY width, nome and cutoff.
Its exact input is
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialKineticMarginals.lean:198`,
`kineticWeight_upper_marginal`. No heat positivity or late-cutoff guard is
needed for this algebraic normalization.

The actual original width-two transfer instead has the exact face test

```
H[P*T1] = w^12*(alpha+alpha^5/16),    alpha=2*w^3.
```

- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCubeHeatOnlyObstruction.lean:91`,
  `tested_original_one_exact`; `:99`, `tested_original_one_positive`.
- Inputs:
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCubeAllCutoffTestedTransfer.lean:102`,
  `tested_vacuum_transfer_pin`, and
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCubeVacuumActionMoment.lean:156`,
  `tested_vacuum_action_channel`. Exact original fringe integration retains
  the full spatial action; no six-face surrogate or raw expansion is used.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteHaar.lean:52`,
  `plaquette_mean_zero`, makes the same physical face test zero on every
  constant.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCubeHeatOnlyObstruction.lean:112`,
  `original_one_not_constant`; `:126`, `original_one_not_free`, therefore
  prove tested inequivalence to every scalar constant and to every free
  kinetic vacuum marginal on this slice, whatever its nome/cutoff.

Scope: original width 2, K=1, w>0. Strictness concerns the tested numerator,
NOT positivity of the whole cutoff action or a normalized probability law.
This does not identify the ambient gluedMiddle endpoint marginal with T1,
nor rule out every selected interacting kinetic-plus-spatial coarse action.

## Verification and next actual join

Two serialized monitored focused checks passed all six retention gates and
five heat-only gates, each within {propext, Quot.sound}. Independent read-only
review confirmed the mathematics, four-lag time count and stated boundaries.
Final logs, SHA-256:

- `/private/tmp/ym-oct7-rg-slow-state-retention.log`:
  `075764dcc87be6c2a661c5d4caabc9b06e26fe67f129faab0987eb990a0ea584`.
- `/private/tmp/ym-oct7-cube-heat-only-obstruction.log`:
  `9916584648d63374aa2a0a5138d94005313702dc46b37afabf37c1413ddcd35d`.

One 20-GiB compiler, 12-GiB reserve, dynamic capacity checks and zero swap.
Namespace/notation elaboration failures were repaired and are not evidence.
No source holes, new axioms, classical input, changed canonical fields or
raised heartbeats. Root imports registered; no full-root/tree build or audit,
hashed-baseline regeneration or CI enablement.

NEXT bounded exact join: identify the endpoint marginal of the actual ambient
`gluedMiddle` with the canonical slice first-message test, keeping endpoint
spatial factors separate. This exposes the signed original-action discrepancy;
it does not estimate it. An actual retained/coarse form comparison with useful
delta budget, independent AF survival, normalized scaling/volume control,
limiting SAME OS/QFT theory, every group and Clay remain OPEN.
Canonical broad chart unchanged; no reprint.
