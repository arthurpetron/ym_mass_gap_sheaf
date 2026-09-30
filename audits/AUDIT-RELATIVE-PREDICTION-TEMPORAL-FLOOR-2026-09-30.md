# Original-action relative prediction and temporal-energy floor

Date: 2026-09-30 UTC. Whole-project Clay target OPEN.
Classification: PROGRESS. All eleven focused module checks passed; 39
printed axiom gates are within {propext, Quot.sound}. Chart unchanged.

## The mathematical step back

The old local lower coefficient used a global heat-minimum comparison.
This argument instead keeps the full original density W and its signed
angular derivative. For a head-linear fundamental character f and any
supported head-independent polynomial predictor q, put

    g = f-q, Z = H[W], A = H[W*g^2], F = H[W*f^2],
    E = H[W*Gamma(f)], R_h = sum_D H[h*(D W)*(D f)].

The six angular directions are the SU(2) quaternion generators. Generalized
integration by parts gives E+R_f=3F and E+R_g=3H[W*g*f]. The Casimir value
three and the fundamental-character identity Gamma(f)+f^2=4 are actual
SU(2) inputs, not compact-group-independent claims.

Certificates CW +/- DW supply, for every rational t,

    +/- 2*t*R_h <= 6*C^2*H[W*h^2] + t^2*E.

Using t=2*C^2 for h=f yields 3F <= 2*(1+C^2)*E. Using t=1 for h=g, then
the positive weighted square (4*(1+C^2)*g-f)^2, yields
E <= (24+36*C^2)*A. With E+F=4Z, rational cancellation gives

    Z <= (5+2*C^2)*(2+3*C^2)*A.

No square root, conditional-density reciprocal, discarded cross term, or
independence of the action and predictor is used. Normalization divides
only by the SAME positive original partition.

## Supplied declaration path

Paths in this section are relative to `lean/YMGap/Continuum/`.

- `QuaternionHaarGeneralizedLinearWard.lean:106`, `generalized_linear_ward`,
  and line 124, `independent_shift_ward`, preserve the signed full-weight
  residual. `residual_lower_scaled` at line 249 and `residual_upper_scaled`
  at line 283 provide both scaled Young bounds.
- `RationalRelativeWardPrediction.lean:21`, `predictionFactor`, defines
  (5+2*C^2)*(2+3*C^2). `prediction_bound` at line 131 proves the scalar
  elimination, and `normalized_prediction_bound` at line 171 cancels the
  same positive partition. `predictionFloor` at line 32 is its explicit
  positive rational reciprocal.
- `QuaternionHaarRelativePredictionFloor.lean:107`, `raw_prediction_floor`,
  and line 151, `normalized_prediction_floor`, combine those ingredients for
  supported polynomials and the displayed relative/kinematic certificates.
  These are generic consumers; the next three modules supply their inputs.
- `BF4ExactSlabSelectedPlaquetteDegree.lean:38`,
  `faceCharacter_head_degree_one`, and line 63, `linkLocal_head_degree_zero`, derive
  the degree conditions from the actual physical face and link-locality.
- `BF4ExactSlabFixedSpatialPlaquetteAngularSquare.lean:238`,
  `oriented_fourWord_first_angularSquare_of_exposure`, and line 297,
  `fullSlabFaceCharacter_head_angularSquare`, transport the fundamental
  kinematics through explicitly constructed four-block exposure and the
  actual first-link head swap. Equalities retain arbitrary Haar insertions.
  No one-slice spatial carrier is identified with the full slab by assumption.
- `BF4ExactSlabSelectedActionRelativeBound.lean:261`,
  `selectedActionRelativeBound`, retains the complete supplied physical
  face list. The selected star has at most six factors because the list is
  explicitly duplicate-free; the entire complementary action remains and
  has zero derivative in the selected link. It supplies
  C(w)=6*relativeCap(w,2048), for K>=relativeCutoff(w,2048).
- `BF4ExactSlabRelativePredictionError.lean:75`, `raw_prediction_bound`, and
  line 137, `finite_prediction_floor`, supply the actual original joint-action
  instance. Every supported polynomial q localized away from the FIRST
  physical edge of the plaquette is covered. The normalized conclusion
  uses the existing `finiteValue`, not a replacement probability law.
- `BF4ExactSlabFixedSpatialPlaquetteEnergyFloor.lean:216`,
  `plaquette_jump_originalFiniteValue`, exposes the exact existing
  full-window pin independently of which lower coefficient is applied.
  The old `plaquette_energy_floor` statement is preserved.
- `BF4ExactSlabFixedSpatialRelativeEnergyFloor.lean:61`,
  `plaquette_relative_energy_floor`, uses the literal upper-time character
  as predictor for the lower one. The density is the COMPLETE chain action
  on extent width+2*n+2, with 2*n+1 transitions. The conclusion is
  relativePredictionFloor(w) <= 2*normalizedEnergy of the original source.
- `BF4WilsonAllNomeRelativePlaquetteEnergyFloor.lean:59`,
  `relativeStageCutoff`, gives the explicit late-stage threshold.
  `plaquette_relative_timeIncrement_floor` at line 93 uses the existing original
  joint diagonal convergence, and `plaquette_relative_defect_form_floor` at line 107
  uses the unchanged exact completed increment pin. Its target is
  <v,(I-T)v> >= relativePredictionFloor(w)/2 on the SAME literal Wilson
  completion and physical-time transfer, for the existing centered plaquette v.

## Coefficient versus cutoff

Write r(w)=relativeCap(w,2048), C(w)=6*r(w), and
s(w)=1/[(5+2*C(w)^2)*(2+3*C(w)^2)].

The source definitions expand algebraically, for 0<w<1, to

    r(w) = 1 + 4096*w / ((1-w)^3*(1+w)).

This expansion is a reading of the rational definitions, not an added Lean
asymptotic theorem. The definitions are `JacobiHeatRelativeAngularBound.lean:46`,
`relativeCost`; `JacobiShiftedRelativeSlope.lean:33`, `budget`;
`HeatKernelConv.lean:461`, `HKConv.Cstar`; `HeatKernelPos.lean:150`,
`HKPos.factorLB`; and `HeatKernelConvGen.lean:335`, `HKConvGen.geoTailBase`.
None contains the global heat-product minimum. `relativeCap` is defined at
`QuaternionHaarHeatRelativeAngularBound.lean:41`.

`QuaternionHaarHeatRelativeAngularBound.lean:44`, `errorTolerance`, DOES contain
headFloor(w). Consequently `relativeCutoff` at line 46 still depends on that minimum
and the explicit value/derivative deficit moduli. Removing this dependence
from the coefficient does not remove it from the required precision.

| Quantity | Quantified uniformity | Remaining dependence |
| --- | --- | --- |
| C(w), s(w) | Extent, physical face-list length, width, boundary depth, sufficiently late heat cutoff | Explicit nome w; fixed numerical derivative budget 2048 |
| relativeCutoff(w,2048) | Same threshold for the supplied finite physical family at fixed w | Nome, heat minimum, deficit moduli |
| Original partition | No uniform size asserted; canceled only against its own numerator | All parameters of the original finite action |
| Completed defect form | All physical spatial plaquettes and widths at fixed w | Nome and the chosen single observable; not every state |

No beta-independent coefficient, spacing-independent floor or asymptotic
comparison with starRatio is asserted by these declarations.

## Proof boundary and next mathematical test

The bound is a prediction floor for an actual local observable, and its
completed temporal-energy consequence. It is NOT a spectral gap for every
vacuum-complement state, a construction for every compact simple group,
nontrivial continuum survival, or the Clay theorem. Angular integration
by parts is not itself a physical-time generator identification; the
temporal conclusion uses the separately proved original-window pin.

The next test is the normalized observable at the SAME matched physical
time along a justified changing-coupling/spacing family. A positive fixed-
nome form value does not establish finite physical mass or a surviving
continuum excitation. The previously proved unnormalized plaquette defect
can still vanish as w approaches one. Neither conditional-projector
idempotence nor a single covariance loss may be treated as iterated decay.

No canonical Clay field or ASCII-chart state is changed by this support
increment. No new analytic premise, carrier substitution, axiom or sorry
was added. No existing ledgered sorry is discharged by these results.

## Verification

All checks used the monitored safe launcher, one worker, a hard 20 GiB
worker cap, 12 GiB OS reserve and dynamic pressure/swap monitoring. The
main agent serialized all builds; Sol and Luna worked on separate proof
pieces and read-only reviews. Memory thresholds were not raised.

| Focused module | Gates | Final log under `/tmp/` |
| --- | ---: | --- |
| QuaternionHaarGeneralizedLinearWard | 7 | ym-generalized-ward-20260930.log |
| RationalRelativeWardPrediction | 6 | ym-rational-ward-prediction-20260930.log |
| QuaternionHaarRelativePredictionFloor | 4 | ym-relative-prediction-floor-20260930.log |
| BF4ExactSlabSelectedPlaquetteDegree | 2 | ym-selected-plaquette-degree-20260930.log |
| BF4ExactSlabFixedSpatialPlaquetteAngularSquare | 4 | ym-plaquette-angular-square-20260930.log |
| BF4ExactSlabSelectedActionRelativeBound | 1 | ym-selected-action-relative-20260930.log |
| BF4ExactSlabRelativePredictionError | 3 | ym-relative-prediction-error-20260930.log |
| BF4ExactSlabFixedSpatialPlaquetteEnergyFloor | 2 | ym-plaquette-jump-pin-20260930.log |
| BF4ExactSlabFixedSpatialRelativeEnergyFloor | 1 | ym-relative-energy-floor-20260930.log |
| BF4WilsonAllNomePlaquetteEnergyFloor | 5 | ym-wilson-plaquette-source-pin-20260930.log |
| BF4WilsonAllNomeRelativePlaquetteEnergyFloor | 4 | ym-wilson-relative-energy-floor-20260930.log |

All 39 printed gates are within {propext, Quot.sound}, with no sorryAx.
Earlier failed draft checks are not counted as verification. Two expensive
dependent reductions were resolved by abstracting the quaternion/exposure
witness before specializing to the physical carrier; no mathematical
hypothesis was added to the final physical statements.

No full-root build, broad audit or frontier guard is claimed. Root imports
were registered but the aggregate root was not built. CI remains disabled.
