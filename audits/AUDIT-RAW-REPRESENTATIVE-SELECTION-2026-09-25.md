# Audit: raw same-object representative-selection boundary

## Result

The existing BF4 machinery constructs the concrete fixed-family carrier,
transfer, vacuum-complement vector, and RC-valued same-object correlator.  For
the fixed geometric family, the moving-cube vector and every completed
transfer power are themselves built from explicit Cauchy presentations.  The
literal CReal representative can therefore be constructed without quotient
choice.  The remaining raw input is now only its cross-scale variation
certificate.

## Evidence

| declaration | location | evidence |
|---|---|---|
| `centralPhysicalDynamicMovingCubeRCChannel` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorSameObjectRCChannel.lean:195` | Bundles the literal moving-centered completed vector, its positive norm floor, and the same-object channel for every dynamic scale. |
| `sampledConnectedAutocorrelation_eq_global` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorScheduledRCChannel.lean:120` | Identifies the sampled RC correlator with the global completed adaptive-transfer matrix coefficient of that same vector. |
| `centralPhysicalCutoffCompletedInner` | `lean/YMGap/Continuum/BF4PhysicalCutoffLinearCompletedInner.lean:47` | Descends the physical pairing to `CReal.RC` by quotient lifting the representative pairing. |
| `physicalCauchyPairingLimit_welldef` | `lean/YMGap/Continuum/BF4PhysicalCutoffLinearCompletedInnerWellDefined.lean:216` | Supplies `CReal.Equiv` between pairing limits for two completion representatives, which is exactly what is needed for the RC quotient descent. |
| `MovingCubeRawScheduledRepresentativeVariation` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler.lean:47` | Requires an actual `CReal` stream, exact `represents` equalities into the sampled RC channel, and `SummableCRealStepVariation`. |
| `marginalHalfGeometricRawRepresentative` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.lean:210` | Uses the explicit moving-centered Cauchy presentation and recursively explicit adaptive-transfer Cauchy maps to define the raw CReal pairing representative. |
| `marginalHalfGeometricRawRepresentative_represents` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.lean:525` | Proves exact quotient equality with the literal sampled same-object RC correlator. |
| `MarginalHalfGeometricRawRepresentativeVariation.toRawScheduledVariation` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.lean:547` | Factors the remaining obligation to a single `SummableCRealStepVariation` field for the explicit representative stream. |
| `marginalHalfGeometricRawRepresentativeCanonical` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.lean:248` | Repeats the same construction with fixed decidable nome proofs, removing proof-argument variation from the fixed-family stream. |
| `marginalHalfGeometricRawRepresentativeCanonical_represents` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.lean:330` | Proves the canonical CReal stream has the same literal sampled RC correlator. |
| `marginalHalfGeometricRawCanonicalZeroTimeVariation` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.lean:478` | Closes the complete `SummableCRealStepVariation` field at time zero; positive-time cross-scale variation remains open. |

## Generic constructive boundary

`CReal.Equiv` is the constructive-real identification relation used by the
quotient `CReal.RC`; it is not definitional equality of `CReal` values.  Thus
`physicalCauchyPairingLimit_welldef` alone cannot be used as a generic
`Quotient.lift` into `CReal`.  The fixed-family construction avoids this by
retaining the explicit Cauchy presentations already used to build the moving
cube and transfer powers.  A generic family still needs an explicit compatible
presentation certificate; hidden quotient choice remains disallowed.

## Current fixed-family boundary

The exact representative and its `represents` equality are now proved in the
specialization module.  A proof-argument-canonical copy has the same exact
RC stream, and its time-zero variation is now inhabited with an explicit
inner modulus.  The only remaining uninhabited all-time field is the
summable consecutive-scale variation modulus at positive physical times.  No
representative-selection gap is being counted twice.

This boundary does not weaken the finite same-object result and does not claim
a continuum or Clay conclusion.  It precisely isolates the next causal
frontier: representative selection plus variation for the SAME moving-cube
correlator.
