# Affine variance calibration audit — 2026-09-21

## Result

The tested bound-to-bound route cannot certify a positive one-step response or
a linear-spacing calibration.  This is a limitation of the present explicit
certificates, not a statement about the actual response.

For strict rational nome `0 < w < 1`, write `d = 1-w` and let `F(w)` be the
constructed affine `varianceFloor`.  The checked scalar chain is

`600*F(w) <= d^48 <= d`.

The first-factor Euler estimate and its propagation to the retained head
floor are `eulerFloor_le_nome_defect`,
`heatFloor_le_nome_defect_square`, and
`headFloor_le_nome_defect_square` in
[`BF4ExactSlabHeadFloorNomeCeiling.lean`](../lean/YMGap/Continuum/BF4ExactSlabHeadFloorNomeCeiling.lean#L24-L72).
The boundary-window and reciprocal consequences are
`boundary_lower_le_defect_power`,
`sixHundred_floor_le_boundary_lower`, and
`sixHundred_floor_le_defect_power` in
[`BF4ExactSlabPlaquetteAffineCalibrationObstruction.lean`](../lean/YMGap/Continuum/BF4ExactSlabPlaquetteAffineCalibrationObstruction.lean#L40-L78).

The available completed single-plaquette loss budget is `192*d` at one lattice
step.  Relative to this particular lower witness, `computedLossRatio_ge`
proves `115200 <= 192*d/F(w)`, while `subtraction_floor_nonpositive` proves
`F(w)-192*d <= 0`
([obstruction module, lines 95–134](../lean/YMGap/Continuum/BF4ExactSlabPlaquetteAffineCalibrationObstruction.lean#L95-L134)).
Thus subtracting these two available bounds cannot establish positive
survival.  Neither inequality bounds the actual variance from above or the
actual time loss from below.

The `192*d` loss estimate itself has a geometric guard:
`BF4AllNomeCompletedPlaquetteIncrement.completed_loss_nome_bound` requires
every loop edge to be active
([lines 81–105](../lean/YMGap/Continuum/BF4AllNomeCompletedPlaquetteIncrement.lean#L81-L105)).
Strict padding supplies that premise through
`BF4ExactSlabFixedSpatialWilsonActivePadding.includedLoop_edges_active`
([lines 47–57](../lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonActivePadding.lean#L47-L57)).
The scalar obstruction alone is not an actual-loss theorem for an arbitrary
boundary face.

## Existing whole-signed lag control

`BF4WilsonTimeZeroMomentConvexity.timeIncrement` accepts any complete signed
time-zero `WindowExpression`; `timeIncrement_pin` gives its exact polarization,
and `timeIncrement_linear` bounds its `n`-step increment by `n` times the
one-step increment without splitting its signed cross terms
([lines 153–203](../lean/YMGap/Continuum/BF4WilsonTimeZeroMomentConvexity.lean#L153-L203)).
For one active Wilson loop,
`BF4WilsonAllNomeTimeIncrement.timeIncrement_nome_bound` gives
`24*n*length^2*d`; a fundamental plaquette has the resulting ordinary
one-step budget `384*d`
([lines 120–127](../lean/YMGap/Continuum/BF4WilsonAllNomeTimeIncrement.lean#L120-L127)).

The completed signed plaquette family is already an actual vector:
`familyExcitation_norm_floor` supplies its norm floor and
`familyExcitation_correlator_pin` identifies its completed time pairing with
the same connected joint moment
([`BF4ExactSlabFixedSpatialPlaquetteFamilyVariance.lean`, lines 151–185](../lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteFamilyVariance.lean#L151-L185)).
What is absent is the join from that family to a quantitative whole-family
one-step upper estimate.

In the inspected modules, no checked theorem proves
`oneStep(F) <= C(w)*sum_p c_p^2` without a family-cardinality factor.  A finite
Cauchy–Schwarz aggregation of the individual loop estimates suggests a
fallback with a `qs.length` loss, but that family aggregation and its
`familySpan`/Wilson-expression identification are not implemented.  The
resulting formula must not be cited as a checked declaration.

## Checked obstruction and interpretation

`computedLossRatio_no_linear_scaling` is pointwise in an arbitrary strict
nome and shows that this computed quotient cannot be bounded by `M*a_j` once
the supplied spacing modulus makes `M*a_j <= 1`
([lines 136–151](../lean/YMGap/Continuum/BF4ExactSlabPlaquetteAffineCalibrationObstruction.lean#L136-L151)).
It can be re-instantiated with a different nome at each index, but it is not a
packaged theorem about a nome sequence.  It does not refute linear control of
the actual normalized loss or physical survival.

The dependency-complete
`+YMGap.Continuum.BF4ExactSlabPlaquetteAffineCalibrationObstruction:olean`
target passed. Two final serialized direct checks reported ten clean printed
gates (3 helper, 7 consumer), all within `{propext, Quot.sound}`, without
warnings or `sorryAx`. One monitored 20 GiB worker was used under the safe
build policy; no full-root audit was run. Logs:

- `/tmp/ym-gap-affine-calibration-build.log`
- `/tmp/ym-gap-BF4ExactSlabHeadFloorNomeCeiling-final.log`
- `/tmp/ym-gap-BF4ExactSlabPlaquetteAffineCalibrationObstruction-final.log`

## Missing producer

The relevant next analytic input is a relative one-step comparison under the
same original selected action, for the whole signed family, such as

`D_1(F) <= C(w) * Var_W(F)`,

with signed cancellations retained and quantitative control along an actual
chosen spatial/coupling/spacing family. A bound by an arbitrary large C is
not sufficient: its product with the lattice lag representing fixed physical
time must be controlled, for example by a proved linear-spacing budget.
This does not impose an unnecessary all-observables or all-bare-couplings
requirement; the intended scaling family and any support dependence must be
explicit. The existing whole-expression convexity would then propagate the
one-step bound to multiple lattice-time steps. Transporting the same failed
pair of absolute bounds cannot resolve the demonstrated `d^48` versus `d`
mismatch. An improved estimate would need genuinely stronger mathematics.

The full Clay Yang–Mills mass-gap target remains open.  No continuum QFT,
changing-spacing survival, canonical-field construction, all-group theorem,
or refutation of the actual response is established here.
