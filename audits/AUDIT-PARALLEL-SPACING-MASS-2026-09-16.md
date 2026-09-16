# Parallel review: spatial/spacing control and physical mass

Source review: 2026-09-16, against committed milestone `b84fa5e` and the
current shared worktree. This branch changed no Lean source and ran no Lean
compiler. Statements below are source findings, not new kernel verification.
The new union relaxation/row-limit work in progress is not used as evidence
that a continuum obligation has closed.

## Outcome

These are two independently investigable analytic branches, but neither can
be completed by attaching a spacing parameter to the present strict bound.
The fixed-nome spatial limit and strict completed bound already exist.
Changing-action spatial comparison and physical time/mass calibration remain
different obligations. Most scalar calibration machinery is already present;
its missing input is the physical producer, not another wrapper.

The whole-project target remains a nontrivial continuum Yang--Mills theory on
R^4, for every compact simple gauge group, with the required QFT axioms and a
positive physical Hamiltonian gap. None of the results inventoried here closes
that target.

## 1. What is already on the SAME spatial union carrier

| Result | Declaration and source | Exact boundary |
| --- | --- | --- |
| Original-action spatial comparison | `chartScalar_spatial_bound`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialComparison.lean:56` | Fixed `w`; compares recentered boxes with explicit `spatialAmplitude`, and the nome-dependent geometric rate. |
| Actual three-regulator Cauchy diagonal | `spatialCauchy`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialLimit.lean:69`; `spatialLimit`, same file `:78` | Heat cutoff, slab extension and spatial padding vary; `w` does not. |
| Spatial-limit convergence of the original reflected pairings | `jointPairing_spatial_converges`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialLimit.lean:88` | A fixed pair of supplied presentations and fixed nome. |
| Base-box independence | `spatialPairing_inclusion`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBaseCoherence.lean:294` | Retains the literal face words under a larger support guard; not a change of lattice spacing or coupling. |
| One completion allowing unbounded support bases in a Cauchy stream | `Stage`, `lean/YMGap/Continuum/BF4SpatialUnion.lean:38`; `UnionCompletion`, `lean/YMGap/Continuum/BF4SpatialUnionSeminorm.lean:126` | One fixed set of nome/smallness parameters. |
| Actual discrete time on that completion | `completedTime`, `lean/YMGap/Continuum/BF4SpatialUnionSeminorm.lean:130`; `completedTime_add`, same file `:137` | Parameter is `Nat`; no physical spacing appears. |
| Fixed-base completion enters the same union | `completionMap`, `lean/YMGap/Continuum/BF4SpatialUnionFixedBase.lean:79`; `completedInner_map`, same file `:112`; `completionMap_time`, same file `:118` | Preserves pairing and time at the same nome. |
| Strict completed form bound | `completed_twoStep_form_gap`, `lean/YMGap/Continuum/BF4SpatialUnionCompletedGap.lean:153` | Every vector orthogonal to the actual unit; `T 2`, with `q(w)=twoStepRate w hd`. |
| Rate and its strictness | `twoStepRate`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialDenseGap.lean:65`; `twoStepRate_lt_one`, same file `:72` | `q(w)=timeRate(w)^2`; `timeRate`, same file `:48`, is `entropyRate 625 (adjustedCoreRate w hd)`. No spacing parameter. |
| Squared-norm form of the same estimate | `unitComplement_oneStep_norm_gap`, `lean/YMGap/Continuum/BF4SpatialUnionUnitComplement.lean:77` | `B(T 1 x,T 1 x) <= q(w) B(x,x)`; the distinction between one time step and a two-step form matters for calibration. |
| Original nonconstant excitation and correlator | `excitation`, `lean/YMGap/Continuum/BF4SpatialUnionExcitation.lean:57`; `excitation_correlator_pin`, same file `:69`; `excitation_norm_floor`, same file `:92` | The positive lower norm bound is `starRatio w`; not a spacing-uniform continuum excitation certificate. |

## 2. Decisive restrictions on the spacing branch

The current construction requires `heatRemainderBound w < 1` as an argument
of `unionSeminorm` (`lean/YMGap/Continuum/BF4SpatialUnionSeminorm.lean:85`,
with parameter declaration at `:31`). That guard cannot cover the supplied
small-coupling AF chart:

| Existing obstruction | Declaration and source |
| --- | --- |
| The returned remainder cap is at least two for `w >= 1/4` | `remainder_cap_ge_two`, `lean/YMGap/Continuum/BF4SmallNomeAFGuardObstruction.lean:37` |
| The guard forces `w < 1/4` | `guard_forces_small_nome`, same file `:51` |
| The fine nome violates the guard at each chart point `0 < g <= min(g1,1/2)` | `fine_guard_fails`, same file `:91` |
| One matched blocked nome also violates it | `blocked_guard_fails`, same file `:97` |
| A concrete chart point and both cap bounds are returned as data | `obstructionWitness`, same file `:115` |
| Neither fine nor blocked guards can hold throughout the chart | `no_fine_guard_on_chart`, same file `:126`; `no_blocked_guard_on_chart`, same file `:133` |

These statements concern the returned cap, not a lower bound on the actual
heat remainder. They refute reuse of this guard on that chart, not existence
of the AF law or of Yang--Mills theory.

A separate exact rational schedule is already refuted:
`matchedDyadicSameActionAFBridge_uninhabited`,
`lean/YMGap/Continuum/BF4MatchedDyadicHeatObstruction.lean:55`.
Its heat-time equation alone forces a rational square to equal `1/2`, by
`squareTime_dyadicBridge_uninhabited`, same file `:43`.
No consumer requiring this bridge is an available physical instance.

The bridge-free replacement does exist: `matchedWindowFamily`,
`lean/YMGap/Continuum/BF4RoundedPositiveAFWindows.lean:139`, supplies actual
positive local heat windows; `window_spread`, same file `:45`, proves the
spread bound at `bits(w)=5*cutoff(w)+5`, and `bit_heat_cost`, same file `:85`,
bounds its AF heat cost by 180. `retainedHarnack`, same file `:155`, acts on
the displayed product of twenty-three completed heat factors. Its arguments
do not identify that product with the original spatial-union transfer.

## 3. Scalar spacing and mass machinery already available

| Available component | Declaration and source | Inputs not constructed by this component |
| --- | --- | --- |
| Physical spacing on an AF chart | `PhysicalSpacingEnvelope`, `lean/YMGap/Continuum/BF4MatchedPhysicalAFBridge.lean:333` | Positive `a(g)` and `a(g)*Lambda <= C*g^2` are fields, not consequences of the cubic coupling law. |
| Heat-time versus spacing inequality | `heat_time_ge_rate_mul_spacing`, `lean/YMGap/Continuum/BF4AFHeatSpacing.lean:79` | Supplied `AFEnvelope`; gives `(alpha*Lambda/(4*C))*a(g) <= t(g)/4`, not a physical Hamiltonian gap. |
| Explicit spacing-to-zero modulus | `spacingToZeroOfQuadraticEnvelope`, `lean/YMGap/Continuum/BF4AFPhysicalSpacingToZero.lean:103`; `envelopeSpacingModulus`, same file `:96` | Physical spacing envelope and a Type-level `CouplingToZero`, same file `:35`. The AF specialization additionally needs `ShiftedAFTrajectoryIdentification`, same file `:42`. |
| Inverse-square spacing majorant | `spacingInverseSquareTailOfAFTrajectory`, `lean/YMGap/Continuum/BF4AFPhysicalSpacingInverseSquare.lean:88` | Supplied spacing envelope and identified AF trajectory. |
| Fixed physical-distance contraction implies a positive lower mass scale | `FixedDistanceContraction`, `lean/YMGap/Continuum/FixedDistancePhysicalSeparator.lean:53`; `FixedDistanceContraction.floorRate_le_marginRate`, same file `:185` | The SAME separator must satisfy `q_j^depth_j <= macroRate < 1` and `depth_j*a_j <= lengthCeiling`; also requires the supplied correlator interface. Result is `(1-macroRate)/lengthCeiling <= (1-q_j)/a_j`. |
| Exact full-range constructive logarithm | `fullLogMass`, `lean/YMGap/Continuum/PhysicalSeparatorFullLogRate.lean:78`; `fullLogMass_equiv_neg_log`, same file `:98`; `fullMassRate`, same file `:108` | Computes `-log(q_j)/a_j` for supplied separator/spacing. `fullMassRate_posEv`, same file `:113`, is per scale. |
| Exact-log lower comparison | `marginRate_le_fullMassRate`, `lean/YMGap/Continuum/PhysicalSeparatorFullLogComparison.lean:101` | Same supplied separator and spacing. |
| Finite upper mass scale remains separate | `FullRangeLogRateCeiling`, `lean/YMGap/Continuum/PhysicalSeparatorFullLogComparison.lean:163`; `FullRangeExactPhysicalSeparatorCertificate`, same file `:172` | The ceiling is an explicit field; exact per-scale positivity does not supply it. |
| Lower persistence with same-spacing pin | `ExactLogMassNormalizedFlow`, `lean/YMGap/Continuum/ExactLogMassNormalizedPersistence.lean:34`; `uniformExactFloor`, same file `:51` | Rational flow, explicit spacing identification, pointwise lower certificate and persistence input. |
| Physical finiteness forces separator toward one | `LinearMarginTail.toEventualHalfWindow`, `lean/YMGap/Continuum/PhysicalSeparatorLinearTail.lean:136` | Uses `1-q_j <= M*a_j` and `SpacingToZero`, same file `:31`. |

The name `physicalTime` in
`lean/YMGap/Continuum/BF4MatchedPhysicalAFBridge.lean:347` denotes the
**heat-time chart** `4*g^2`. It is not the function `completedTime` acting
on the union carrier. An identification between these two meanings of time
is NOT FOUND in the inspected modules.

Likewise `PhysicalSeparator`, `lean/YMGap/Continuum/PhysicalSeparator.lean:144`,
carries an abstract `CorrInterface` and a geometric bound, not an operator,
Hamiltonian, or spectral-equality field. Instantiating the scalar rate alone
does not identify a physical spectral edge.

## 4. Exact parallel work and rejoin points

| Independent branch | What can be studied before any additional strict-gap work | Required rejoin; current source finding |
| --- | --- | --- |
| Original-action changing-scale comparison | Work on actual normalized numerators with their shared partitions, keeping coupling, support, cutoff and volume explicit. The existing finite consumer is `comparison_bound_eventually`, `lean/YMGap/Continuum/BF4ExactSlabAllNomeFaceSetComparison.lean:64`, whose determinant estimate is an explicit premise. | A replacement for the small-nome spatial estimate, with scale-controlled error and original observables. That consumer currently compares two face sets at the SAME `w`; a changing-`w` union comparison is NOT FOUND in `BF4SpatialUnion*.lean`, `BF4ExactSlabFixedSpatialSpatial*.lean`, `BF4ExactSlabAllNomeFaceSetComparison.lean`. |
| Physical spacing and mass calibration | Establish the existing physical-envelope and same-separator macro-contraction premises, together with finite upper rate control. Scalar logarithms, positive division and spacing-modulus composition do not need to be rewritten. | An original-transfer/physical-length pin and a continuum-compatible observable family. A `UnionCompletion` instance of `FixedDistanceContraction` or `FullRangeExactPhysicalSeparatorCertificate` is NOT FOUND in `BF4SpatialUnion*.lean`, `FixedDistancePhysicalSeparator.lean`, `PhysicalSeparatorFullLogComparison.lean`. |
| Spatial geometry within the fixed-nome branch | The literal translation/recentering operations are available as `translateSpan` and `recenter`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialRecenter.lean:38` and `:91`; they commute with time by `translateSpan_advance`, same file `:83`. | A full spatial-translation action preserving the union limiting form is NOT FOUND in `BF4SpatialUnion*.lean`, `BF4ExactSlabFixedSpatialSpatialRecenter.lean`, `BF4ExactSlabFixedSpatialBaseCoherence.lean`. Recentering and increasing the support guard are not such an action. |

The independent work is therefore substantial analysis and geometry, not
five independent ways to declare a continuum theorem. For the two branches
reviewed here, the earliest common bottleneck is a changing-scale physical
realization; final contraction also needs the same continuum observables,
time semigroup and generator.

`CanonicalSchwingerLimit`, `lean/YMGap/Continuum/CanonicalOSRoot.lean:121`,
already asks for stage maps, observable approximations, expectation bounds,
and separate thermodynamic/continuum moduli. Its `ReferenceWeightStageFamily`,
same file `:84`, requires an actual spacing-to-zero schedule. Neither is
inhabited by the fixed-nome union declarations reviewed here.

`PositiveTimeOSRoot`, same file `:268`, additionally pins the reflected
form, original-algebra representative, transfer representative and positive
probe response to the same limiting functional. A positive norm floor for
the union excitation is not its `probeRayleighLower` field, same file `:330`.

## 5. Shortcuts specifically rejected

1. **Changing a label is not a continuum limit.** The current `twoStepRate`
   is an explicitly nome-dependent bound on `T 2`; `PhysicalSpacing` is only
   a positive rational sequence (`lean/YMGap/Continuum/PhysicalSeparatorLogRate.lean:57`).
   No spacing-to-original-time identification follows from these definitions.
2. **Do not borrow another completed carrier's result.**
   `FixedHalfDynamicVacuumRootLinearFamily.completedGapAt`,
   `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumRootLinearPhysicalBand.lean:75`,
   targets `CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData`,
   not `UnionCompletion`. Its two-sided band and
   `one_sub_epsilon_le_rate`, same file `:141` and `:221`, are conditional
   results for that other family, not an existing union calibration.
3. **Do not turn a scalar name into an operator theorem.** The historical
   `OSReconstruction.ContractionSemigroup`,
   `lean/YMGap/Continuum/OSReconstruction.lean:140`, contains a `Unit` witness,
   not an implemented continuous-time action. It is not a bridge from the
   actual union's discrete time to a physical generator.
4. **Do not repair a divergent bare rate by assuming an additive O(a) error.**
   `BareHeatKernelLinearMarginTail.physicalLinearMargin_impossible_of_bare_escape`,
   `lean/YMGap/Continuum/HKPhysicalLinearMarginTail.lean:153`, already refutes
   that conjunction when the bare rate has the supplied constructive escape
   witness. This does not refute a correctly renormalized comparison.

No new conditional Lean compiler was added: the scalar implications needed
for these branches already exist, while the unsupplied physical estimates
are not consequences of the present fixed-nome carrier theorem. This review
identifies exact reuse and rejects incompatible joins without weakening any
frontier field or manufacturing a physical-mass claim.
