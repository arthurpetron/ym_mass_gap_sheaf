# Original endpoint-weight energy and angular cancellation

Date: 2026-09-21 UTC. The whole-project goal remains OPEN: constructive
continuum Yang--Mills on R^4 for every compact simple group, with nontrivial
same-theory QFT structure, isolated vacuum and finite positive physical mass.

## Proved finite original identity

Let V be the original spatial weight, g the entire endpoint source,
a=V*g, and P the original product kinetic map with its actual active-block
list. The existing temporal energy now has the exact expression

    E_g(f) = H[(a*f)^2] - H[(a*f)*P(a*f)]
             + H[(a*f^2)*(P(a)-a)].

The final correction is not given a sign. In particular, a is not assumed
to be a kinetic eigenvector or a fixed point. No support, positivity,
strict-nome or late-cutoff premise is needed for this algebraic identity.

Source map:

- `endpointSource`, `bareEnergy`, `correction`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGroundStateEnergy.lean:47`,
  `:51`, `:60`, define the full source and both explicit terms.
- `energy_eq_bare_add_correction`, same file at line 144, proves the split.
- The original operator pins used are `transferStep_eq_productMap` and
  `original_quadratic_pin`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferPositive.lean:47`
  and `:55`. `productMap_congr`,
  `lean/YMGap/Continuum/SU2QuaternionProductHeatMarginals.lean:74`,
  transports only coefficient equality; it does not replace the kernel.

## Proved differential cancellation

For one plane rotation D, the explicit polynomial flux is `a*f^2*D(a)`.
Leibniz expansion gives

    (D(a*f))^2 + a*f^2*D^2(a)
      = a^2*(D(f))^2 + D(a*f^2*D(a)).

The original Haar divergence identity removes precisely the last term.
Summing all six planes gives, with the existing angular Laplacian L and
summed square Gamma,

    H[Gamma(a*f)] + H[a*f^2*L(a)] = H[a^2*Gamma(f)].

All weight derivatives cancel; no reciprocal, floor, or derivative bound
for a is needed. Both a and f may be signed. This is an identity, not a
finite-time upper estimate. Arbitrary signed polynomial combinations are
covered without separating their cross terms.

Declarations in
`lean/YMGap/Continuum/QuaternionHaarWeightedAngularCancellation.lean`:
`angularFlux` at line 38, `angular_weight_divergence` at line 42,
`angular_weight_cancellation` at line 80, and
`weighted_angular_cancellation` at line 123.

`endpoint_angular_cancellation`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGroundStateEnergy.lean:173`,
instantiates a=V*g on the original slice carrier. Its only extra guard is
that this carrier has a head block. It does not assume that L generates P.

## No automatic local-to-transfer join

`productMap_independent_of_not_mem`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatMarginals.lean:306`,
proves that an inactive output block is absent from P(f) for every supported
input f. The source explicitly retains unused fringe variables as ordinary
Haar variables, not heat factors (`BF4ExactSlabFixedSpatialKineticMarginals.lean:9`).
Thus one cannot identify the whole polynomial map with angular heat
evolution on every block. The finite cutoff and inactive-slot projections
must be dealt with before any identity-at-zero or generator claim.

The existing `extracted_energy_split`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeProjectionEnergy.lean:97`,
splits constructed *observable* pieces in the actual marginal. This is not
by itself an equality integrating fringe coordinates out of the endpoint
source a while preserving an active observable.

The bounded source inventory found no all-label retained-boundary Schur/
addition theorem for the two-link polynomial kernel in the relative-character,
relative-heat, quadratic-transmission or product-heat modules. The vacuum,
fundamental and quadratic propagation results do not provide that theorem.
`SU2QuaternionRelativeCharacterSelection.solid_specialization` at line 85
specializes the four-word solid, but the inspected
`SU2QuaternionTailEvaluation.lean` has no derivative/Laplacian commutation
theorem. These are separate missing operator identifications, not new
assumed fields or proofs of failure of Yang--Mills.

## Remaining frontier and verification

The correction must stay coupled to the bare energy in a quantitatively
useful comparison for the SAME original operator and variance. The new
identity does not show that the previous terminal derivative budget is
small enough near nome one. It supplies no spatial/spacing estimate,
physical calibration, continuum survival, QFT construction or other-group
realization. No canonical field, analytic premise, hole or axiom changed.

The dependency-complete target
`+YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy:olean`
and both focused checks passed. All eight printed gates are within
`{propext, Quot.sound}`, with no errors, warnings or `sorryAx` in the final
logs. Verification used one monitored 20 GiB worker. No full-root build,
full-tree audit or guard ran; automatic CI remains disabled.

Logs: `/tmp/ym-gap-ground-state-energy-build.log`,
`/tmp/ym-gap-ground-state-energy-check.log`, and
`/tmp/ym-gap-weighted-angular-cancellation-check.log`.

Sol supplied the finite split draft, bounded operator inventory and
independent review of the angular identity (PASS). Main supplied the
divergence argument, six-plane cancellation, original-source consumer,
elaboration fixes and serialized verification.
