# One spatial union carrier, actual strict sector and closed nonzero pilot

Date: 2026-09-16. Baseline: `32bc192`. Previous goal turn: **PROGRESS**.

The whole-project goal remains a constructive nontrivial continuum
Yang--Mills theory on R^4, with the required QFT axioms, isolated vacuum
and positive physical Hamiltonian gap, for every compact simple gauge group.
This checkpoint does not close that goal. It constructs one Cauchy carrier
for the existing finite-base spatial plaquette-character presentations,
with their actual fixed-spacing small-nome SU(2) limiting form and time.

## Checked causal map

All paths are repository-relative. Namespaces match module names except
the four generic modules, whose namespace is `CRealSeminormPairingCompletion`.

| Declaration | Source | Proved connection |
| --- | --- | --- |
| `Stage`, `pairing`, `pairing_at_base`, `distSq_at_base` | `lean/YMGap/Continuum/BF4SpatialUnion.lean:38`, `:120`, `:129`, `:155` | Each element retains a positive support base; pair/distance are computed at its pair's maximum base and agree with every supplied larger common base. |
| `distance_null_congr`, `unionSeminorm`, `UnionCompletion`, `completedTime` | `lean/YMGap/Continuum/BF4SpatialUnionSeminorm.lean:70`, `:85`, `:126`, `:130` | Four-input common-base transport proves limiting radical descent; one explicit-Cauchy quotient admits growing support bases and the actual time semigroup. |
| `PairingData`, `normCeiling`, `diagonal_le_normCeiling` | `lean/YMGap/Continuum/CRealSeminormPairingCompletionBounds.lean:33`, `:69`, `:87` | Dense approximation data, anchor estimate and continuity compute stream bounds; no uniform bound is assumed. |
| `pairRate`, `pairRegularity`, `representativeInner`, `representativeInnerCauchy` | `lean/YMGap/Continuum/CRealSeminormPairingCompletionLimit.lean:70`, `:82`, `:90`, `:102` | Explicit inner/outer moduli construct actual scalar limits and their approximation data. |
| `completedInner`, `completedInner_embedRep`, `representativeInner_unique` | `lean/YMGap/Continuum/CRealSeminormPairingCompletion.lean:78`, `:98`, `:134` | Quotient descent uses supplied Close witnesses; constants retain the dense form and limit uniqueness gives instance pins. |
| `pairingData`, `completedInner_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialGenericPairingPin.lean:36`, `:56` | All generic fields are supplied for the previous fixed-base form; its completed pairing is unchanged. |
| `pairing_anchor`, `pairing_close`, `pairingData`, `completedInner` | `lean/YMGap/Continuum/BF4SpatialUnionPairingData.lean:59`, `:72`, `:101`, `:107` | The union instance discharges every generic field in an explicit common base, on the same union carrier. |
| `closeZeroOfInnerZero`, `completedInner_posdef`, `scalar_contraction_zero` | `lean/YMGap/Continuum/CRealSeminormPairingPosdef.lean:42`, `:71`, `:106` | The computed rate constructs Close-to-zero; positive definiteness and positive-margin cancellation are reusable constructive arguments. |
| `completedInner_posdef`, `completedInner_cauchySchwarz`, `completedInner_time_balance` | `lean/YMGap/Continuum/BF4SpatialUnionGeometry.lean:77`, `:82`, `:98` | Dense zero-distance/CS/time pins instantiate the actual positive-definite union geometry. |
| `centeredMoment_diagonal_pin`, `centered_twoStep_bound` | `lean/YMGap/Continuum/BF4SpatialUnionCenteredForm.lean:83`, `:99` | Each stage's centered moments equal the original spatial moments at its own base; the common strict rate applies before orthogonality. |
| `representativeCenteredMoment_converges`, `completed_twoStep_form_gap` | `lean/YMGap/Continuum/BF4SpatialUnionCompletedGap.lean:73`, `:153` | Three actual pairing limits pass the centered estimate to every completed vector, then orthogonality removes the correction. |
| `UnitComplement`, `unitComplementTime`, `unitComplement_oneStep_norm_gap`, `fixed_twoStep_complement_eq_zero` | `lean/YMGap/Continuum/BF4SpatialUnionUnitComplement.lean:45`, `:47`, `:77`, `:84` | The sector is invariant under actual physical time, with strict one-step squared-norm decay and no nonzero two-step fixed vector in the sector. |
| `liftCauchy`, `liftClose`, `completedInner_map`, `completionMap_time` | `lean/YMGap/Continuum/BF4SpatialUnionFixedBase.lean:49`, `:65`, `:112`, `:118` | Fixed-base maps keep the supplied moduli, mixed pairing and time. They do not represent arbitrary union streams in a fixed base. |
| `excitation`, `excitation_correlator_pin`, `excitation_norm_floor`, `excitation_ne_zero` | `lean/YMGap/Continuum/BF4SpatialUnionExcitation.lean:57`, `:69`, `:92`, `:110` | The original centered base-one plaquette maps to a nonzero union vector, retaining its connected correlators and positive squared-norm floor. |

## Why growing bases do not require a new uniformity assumption

For two stages, compute `N=max(x.base,y.base)`. Their literal face words
are included unchanged into N. `pairing_at_base` consumes the existing
`spatialPairing_inclusion` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBaseCoherence.lean:294`.
Triangle and null-congruence proofs compare respectively three and four
stages in the explicit maximum of their bases. No finite-regulator nullity
is inferred from spatial-limit nullity.

The resulting completion is a quotient of `unionSeminorm.Cauchy`, whose
terms may have unbounded bases. Its data do not include a common base for
the entire sequence. Physical time changes the original distance labels,
not the spatial support guard; `time_cauchy_modulus` at
`lean/YMGap/Continuum/BF4SpatialUnionSeminorm.lean:146` retains the original
modulus verbatim.

For a supplied stream X, the generic completion computes an anchor at
`X.modulus(1)` and a rational ceiling from that term's actual scalar
approximation data. The dense anchor bound gives a ceiling for all later
terms. Pairing continuity at `epsilon^2/(8*(B+1))` supplies an explicit
outer rate; `closedRate` regularizes it. The inner rate is the actual
`pairingCauchy(X_i,Y_i).M`, not a selected modulus or an assumed fixed index.
This is the reusable contraction of the previous physical-specific proof
tower. Both fixed-base and union physical instances supply every field.

The scalar centered moment of a stage x is identified at x.base itself.
Thus the bound from `spatialEvenMoment_first_le` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialDenseGap.lean:133`
holds independently at every X_k with the same `twoStepRate(w,hd)`.
Actual scalar limit convergence then proves

```text
C_2(v,v) <= rho(w)^2 C_0(v,v)                   for every completed v
B(v,T_2 v) <= rho(w)^2 B(v,v)                  when B(v,U)=0
B(T_1 v,T_1 v) <= rho(w)^2 B(v,v)              on that same complement.
```

Here `C_n(v,z)=B(v,T_n z)-B(v,U)B(U,z)`. No orthogonal approximants or
uniform coefficient/support bounds are assumed. Even-time nonnegativity
is retained; one-step positivity is not asserted. The time maps are the
original discrete physical advance, not heat-bath dynamics. Completed
linearity and a continuum Hamiltonian have not been constructed here.

## A closed nonzero physical instance, not unsupplied guards

`BF4SpatialUnionSmallNome` instantiates the entire new carrier/sector at
the existing rational nome `1/1024`. Its `excitation : Sector` is data and
its nonzero theorem has no coupling-guard arguments. The universal gap
still quantifies over the entire sector, not only this witness:

- `Completion`, `Sector`: `lean/YMGap/Continuum/BF4SpatialUnionSmallNome.lean:35`, `:36`.
- `rate_positive`, `rate_lt_one`: `lean/YMGap/Continuum/BF4SpatialUnionSmallNome.lean:48`, `:49`.
- `excitation`, `excitation_ne_zero`, `excitation_norm_floor`: `lean/YMGap/Continuum/BF4SpatialUnionSmallNome.lean:52`, `:56`, `:60`.
- `twoStep_gap`: `lean/YMGap/Continuum/BF4SpatialUnionSmallNome.lean:66`.

The existing nome is defined by `nome` at
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteSmallNomeCertificate.lean:32`.
The closed rate guard is supplied by `existingNome_entropyRate` at
`lean/YMGap/Continuum/BF4ExactSlabSummableCoreRate.lean:37`; no new
numerical estimate or external certificate is trusted.

For general allowed nome, `excitation_correlator_pin` identifies the
actual union vector/time pairing with `centeredMoment`. Its fixed-base
pin leads back to `originalConnected_diagonal_converges` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialCenteredForm.lean:127`.
Its squared norm is at least `starRatio(w)>0`, the original local-star
floor. This is not continuum nontriviality or a constructed particle.

## Scope and unchanged analytic obstruction

The quantified construction retains `0<w<1`, `heatRatio(w)<=1/2`,
`heatRemainderBound(w)<1`, and
`rho(w)=entropyRate 625 (adjustedCoreRate w hd)<1`. Rate and norm floor
depend on coupling. Stream moduli retain their actual data dependence.
No all-beta or lattice-spacing-uniform estimate is claimed.

The existing `guard_fails` and `guard_forces_small_nome` at
`lean/YMGap/Continuum/BF4SmallNomeAFGuardObstruction.lean:45` and `:51`
show that the returned small-nome cap cannot be below one when `w>=1/4`.
`no_fine_guard_on_chart` and `no_blocked_guard_on_chart` at `:126` and
`:133` rule out using that guard throughout the supplied AF chart. This
is an obstruction to reusing the estimate, not a refutation of the
physical theory or a lower bound on the actual heat remainder. This
checkpoint does not remove it.

Stage coverage is exactly the union of the existing positive-base
physical presentation carriers: finite signed sums/products of spatial
plaquette characters with natural time-distance labels. Full signed-coordinate
spatial translation, density in the required gauge observable algebra,
full Hilbert/OS/QFT realization, physical-scale control, continuum passage
and nontriviality, and all compact simple groups remain open. No canonical
frontier field has been closed or weakened.

## Next consumer: completed operations and actual unit projection

The next source-reviewed step is the common-base proof of addition's
squared-distance bound and rational scaling's squared-distance identity.
Existing consumers are
`SquaredSeminorm.BinaryQuadraticLipschitz.mapCauchy` / `completionMap` at
`lean/YMGap/Continuum/CRealSeminormCompletion.lean:449` / `:502`, and
`SquaredSeminorm.ModulusContinuous.mapCauchy` / `completionMap` at `:353`
/ `:377`. These construct operations on the same quotient with explicit
moduli. This next union instance is not yet implemented.

An actual all-vector projection/centering then has the existing patterns
`unitProjectionCauchy`, `unitProjection` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialUnitProjection.lean:76`, `:95`,
and `center_orthogonal`, `center_decomposition` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredCompletion.lean:103`,
`:134`. The coefficient should come from the actual `representativeInner`
and `representativeInnerCauchy`; no representative of an arbitrary RC value
is selected. Its consumer is the missing full stationary vacuum-span
characterization. Current fixed-point exclusion concerns only the unit
complement.

Metric completeness is a separate interface issue. The old
`GeneralCompletionCauchy` at `lean/YMGap/Continuum/GNSComplete.lean:323`
explicitly takes `pt : Nat -> CauchyGNS D` and a modulus as data; its `lim`
at `:382` does not construct representatives of an arbitrary stream of
quotient vectors. Such a lift is not supplied here. `physicalHilbert` at
`lean/YMGap/Continuum/CanonicalOSRoot.lean:513` uses that interface, but
`PositiveTimeOSRoot.positive` at `:272` is `GNSData`, whose `B` at
`lean/YMGap/Continuum/GNSQuotient.lean:102` is rational-valued. It cannot
be substituted for this CReal-valued limiting form without a bridge.
`CRealPreHilbertData` at
`lean/YMGap/Continuum/BF4PhysicalCutoffLinearRadicalDescent.lean:189`
retains CReal values but does not supply this completion construction.

## Verification boundary

Fifteen focused one-worker/20 GiB checks passed, each through the monitored
launcher with a fresh process/swap check. All 180 printed public gates
were within `{propext, Quot.sound}`. Final logs have no errors, warnings,
sorryAx, classical dependency or native-reduction axiom. Initial failed
attempts involved an overly strong literal scalar equality, an explicitly
irreducible definition needing to be unfolded, and projection syntax in
local notation; corrected targets were rechecked. Failed runs do not count
as verification. No existing proof or canonical field was edited; the
root module only gained the fifteen imports. Root/full-tree builds and
the full audit were not run. CI remains manual-only. No new literature
scan ran; the cached review and minimum 12-hour interval remain in force.

Independent source review checked the common-base/nullity argument,
Type-valued moduli, concrete pairing data, mixed-pairing/time maps,
nonzero witness and completed-sector estimate. The next-consumer review
is planning evidence, not a newly proved completeness/projection theorem.

Final local log hashes (SHA-256 of logs, not sources):

| Log under `/tmp/` | Gates | SHA-256 |
| --- | ---: | --- |
| `ym-spatial-union-20260916.log` | 29 | `d788237785b55b9a439ad86d31d27f6aa1e77249b8975e54f1b03417ed4722ce` |
| `ym-spatial-union-seminorm-20260916.log` | 18 | `c9db19ddd5e12803736754ffce8cc89ccef3978d290908f55ff84ddbdf827329` |
| `ym-generic-pairing-bounds-20260916.log` | 8 | `bda8f31cff357d7cdcf9f01c7c3fcb6421876d59df76d3ae29b21afce3cb3f68` |
| `ym-generic-pairing-limit-20260916.log` | 14 | `326feeea06962070b450bc8df0c36960a222566852cdce30938b274ac16a7c63` |
| `ym-generic-pairing-completion-20260916.log` | 13 | `299d1ff39441f92f6c13350c22e0a2d1f8ee708c9578f827430ea8e7b763b8da` |
| `ym-spatial-generic-pairing-pin-20260916.log` | 3 | `6dd2536e1a937868ab1228185546a2a9507cab88f60767b3e53219ab033464ea` |
| `ym-spatial-union-pairing-data-20260916.log` | 11 | `69ea15355229b46b4b2bf9e622b3309b813ab02d8e58b620a7af937ddfc0e228` |
| `ym-spatial-union-centered-form-20260916.log` | 7 | `90fcac941d40560c2bbc1f9359ce5d1a0cc1aacaf41e239968a9d084c1391918` |
| `ym-spatial-union-completed-gap-20260916.log` | 11 | `d09cc841763449513ab395c2f666cbd030287ded6ef6ea880a536ead97a4619d` |
| `ym-spatial-union-fixed-base-20260916.log` | 13 | `f0f84d3d9d4338f791e405015e8584eb2d1f339dc4dc98d5e60e8f93a8ba6742` |
| `ym-generic-pairing-posdef-20260916.log` | 8 | `12e9fde26e0f1c306bd3ed93b1b7d498baa4175b667d632991216f4747207d14` |
| `ym-spatial-union-geometry-20260916.log` | 10 | `e6e35f216cd2e4158662c862c56b81f499b155a43e5f47f50c86e7c7c7f00188` |
| `ym-spatial-union-unit-complement-20260916.log` | 12 | `06c74cce9687403d33a897be1f07206b71bc4fa5fe2feb5d1227b50342231d4e` |
| `ym-spatial-union-excitation-20260916.log` | 11 | `d5fb99875e6f1915e787a7c6834c2064cced9988a58284e13c304f8957f02e32` |
| `ym-spatial-union-small-nome-20260916.log` | 12 | `ec4741250c8e25c66276f7759b008c2ac6419be71b0b6b2fa11d8e494d3ffb7b` |
