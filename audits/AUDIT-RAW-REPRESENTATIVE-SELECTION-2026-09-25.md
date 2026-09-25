# Audit: raw same-object representative-selection boundary

## Result

The existing BF4 machinery does construct the concrete fixed-family carrier,
transfer, vacuum-complement vector, and RC-valued same-object correlator.  It
does not construct a canonical CReal representative of that RC correlator.
The remaining raw input is therefore a genuine representative-selection plus
cross-scale-variation certificate, not an absent finite carrier.

## Evidence

| declaration | location | evidence |
|---|---|---|
| `centralPhysicalDynamicMovingCubeRCChannel` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorSameObjectRCChannel.lean:195` | Bundles the literal moving-centered completed vector, its positive norm floor, and the same-object channel for every dynamic scale. |
| `sampledConnectedAutocorrelation_eq_global` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorScheduledRCChannel.lean:120` | Identifies the sampled RC correlator with the global completed adaptive-transfer matrix coefficient of that same vector. |
| `centralPhysicalCutoffCompletedInner` | `lean/YMGap/Continuum/BF4PhysicalCutoffLinearCompletedInner.lean:47` | Descends the physical pairing to `CReal.RC` by quotient lifting the representative pairing. |
| `physicalCauchyPairingLimit_welldef` | `lean/YMGap/Continuum/BF4PhysicalCutoffLinearCompletedInnerWellDefined.lean:216` | Supplies `CReal.Equiv` between pairing limits for two completion representatives, which is exactly what is needed for the RC quotient descent. |
| `MovingCubeRawScheduledRepresentativeVariation` | `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler.lean:47` | Requires an actual `CReal` stream, exact `represents` equalities into the sampled RC channel, and `SummableCRealStepVariation`. |

## Constructive boundary

`CReal.Equiv` is the constructive-real identification relation used by the
quotient `CReal.RC`; it is not definitional equality of `CReal` values.  Thus
the existing `physicalCauchyPairingLimit_welldef` cannot by itself be used as a
`Quotient.lift` into `CReal`.  A choice-free raw completion theorem needs one
additional explicit certificate that supplies compatible CReal
representatives for the selected completed transfer correlators, together with
their step-variation modulus.  Adding an arbitrary representative or a hidden
choice would violate the repository's constructive gate.

This boundary does not weaken the finite same-object result and does not claim
a continuum or Clay conclusion.  It precisely isolates the next causal
frontier: representative selection plus variation for the SAME moving-cube
correlator.
