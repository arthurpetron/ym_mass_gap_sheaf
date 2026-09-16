# Actual completed spatial pairing, strict sector bound and nonzero excitation

Date: 2026-09-16. Baseline: `fdd1a46`.

The whole-project goal remains a constructive nontrivial continuum
Yang--Mills theory on R^4, satisfying the required QFT axioms and having a
positive physical Hamiltonian gap, for every compact simple gauge group.
This checkpoint concerns the original small-nome SU(2) spatial-limit
reflected form at fixed lattice spacing. It does not close the Clay goal.

## Proved causal connections

Paths are relative to the repository root; declaration namespaces match
their module names. These are actual consumers of the preceding checkpoint's
spatial limits and dense estimate, not newly assumed analytic certificates.

| Declaration | Source | Result / actual consumer |
| --- | --- | --- |
| `diagonalCeiling`, `diagonal_le_normCeiling` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialPairingBounds.lean:42`, `:94` | Actual scalar approximation data and each stream's anchor give an eventual rational norm ceiling. |
| `pairing_close` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialPairingContinuity.lean:87` | Limiting CS and difference identities give quantitative two-sided continuity on the same spatial form. |
| `rawRate`, `pairRate`, `representativeInner`, `representativeInnerCauchy` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialPairingLimit.lean:58`, `:87`, `:105`, `:117` | Explicit outer rate and actual inner regularity construct the mixed scalar limit and its approximation modulus. |
| `representativeInner_welldef`, `completedInner`, `completedInner_embedSpan` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialCompletedInner.lean:76`, `:94`, `:115` | Descends to the already constructed SpatialCompletion, retaining the original dense spatial pairing. |
| `closeZeroOfInnerZero`, `completedInner_posdef`, `completedInner_cauchySchwarz` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialCompletedPosdef.lean:70`, `:96`, `:121` | Actual rate supplies closeness to zero at zero norm; the quotient pairing is positive definite and satisfies sharp CS. |
| `centerApprox_distance` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialCenterAlgebra.lean:119` | Squared distance between rational centerings equals the coefficient-difference square. |
| `centeredRate`, `centeredStream`, `centeredVector` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialCenteredStream.lean:51`, `:54`, `:65` | Constructs a vector in the existing spatial carrier by subtracting actual rational mean approximations. |
| `centeredVector_orthogonal`, `centeredVector_time_pairing` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialCenteredPairing.lean:69`, `:135` | This vector is unit-orthogonal, and its actual physical-time correlations equal the original spatialCenteredMoment. |
| `representativeCenteredMoment_converges`, `completed_twoStep_form_gap` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialCompletedGap.lean:73`, `:153` | Passes the prefactor-free centered bound to every completed unit-orthogonal vector. No orthogonal approximants are assumed. |
| `UnitComplement`, `unitComplementTime`, `unitComplement_oneStep_norm_gap` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialUnitComplement.lean:78`, `:81`, `:118` | The actual physical-time semigroup preserves this sector; time balance gives the strict one-step squared-norm bound. |
| `vacuumMargin_positive`, `fixed_twoStep_complement_eq_zero`, `fixed_oneStep_complement_eq_zero` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialUnitComplement.lean:135`, `:169`, `:178` | Cancelling the explicit positive margin excludes nonzero stationary vectors in the sector. |
| `centralExcitation`, `centralExcitation_norm_floor`, `centralExcitation_ne_zero`, `centralExcitation_correlator_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialCentralExcitation.lean:55`, `:78`, `:85`, `:101` | A concrete original plaquette excitation has positive norm and realizes the same connected spatial correlations under the same time action. |

## Completion uses actual moduli, not a uniform presentation cap

For a scalar `s` with supplied approximation modulus `cs`, the existing
`scalarCeiling` at
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteRealScalarCauchy.lean:52` computes
`abs(s.approx(cs.M(1)))+1`. Apply this to the actual spatial diagonal,
whose QCauchy data were already constructed. For a supplied spatial
Cauchy stream X, set

```text
k_X = X.modulus(1)
C_X = 2 + 2*diagonalCeiling(X.seq(k_X)).
```

The unconditional original anchor inequality passes through spatial limits
and gives `B(X_n,X_n)<=C_X` for `n>=k_X`:
`diagonal_anchor_bound` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialPairingBounds.lean:72`.
No bound on all signed coefficient lists is assumed. For streams X,Y,
the continuity argument uses

```text
C       = max(C_X,C_Y)
delta   = epsilon^2/(8*(C+1))
rawRate = max(max(k_X,k_Y), max(X.modulus(delta),Y.modulus(delta))).
```

`pairRate` closes this supplied rate to the required antitone form.
`pairSequence_regular` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialPairingLimit.lean:100`
unfolds the actual spatialPairing and spatialLimit to their original
`ofQ'CauchySeq` construction; the inner regularity is explicitly
`epsilon.den`. No equality of unrelated approximation indices is assumed.
`representativeInnerCauchy` at `:117` retains the new scalar's explicit
modulus `(epsilon/4).den` from the existing diagonal-limit constructor.

The quotient descent uses supplied Close witnesses and their computed
moduli. It does not select a representative. Positive definiteness is also
quantitative: `pairSequence_limit_close` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialCompletedPosdef.lean:50`
bounds late terms against their actual limit using pairRate itself. Thus
a zero diagonal constructs a Close witness to the constant zero stream.
The scalar helper `late_limit_bound` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCompletedPosdef.lean:38`
is now public; its existing proof is unchanged and its added gate uses
only `propext`.

## Universal completed-sector estimate and fixed-point exclusion

Write B for this completed pairing, U for its actual normalized unit,
and T_n for the already constructed physical-time action on SpatialCompletion.
The scalar centering

```text
C_n(v,z) = B(v,T_n z) - B(v,U)*B(U,z)
```

is defined by `completedCenteredScalar` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialCompletedGap.lean:88`.
Its representative limit comes from three actual pairings and genuine
product continuity. The dense theorem applies to each arbitrary stream
term's centered scalar, not only to orthogonal terms. This proves

```text
C_2(v,v) <= rho(w)^2*C_0(v,v)
```

for every completed v. Only afterwards does `B(v,U)=0` remove the scalar
correction, yielding `B(v,T_2 v)<=rho(w)^2*B(v,v)` on the actual complement.
Time balance and the fixed unit give its invariant time semigroup.
The same estimate is `B(T_1 v,T_1 v)<=rho(w)^2*B(v,v)`.
Even-time forms are nonnegative; one-step positivity is not asserted.

The rate is unchanged from `twoStepRate` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialDenseGap.lean:65`.
The explicit margin `1-rho(w)^2>0` cancels a hypothetical stationary
vector's norm inequality, forcing zero norm, then positive definiteness
forces the zero vector. No norm, possibly zero, is divided out.
This excludes nonzero stationary vectors IN THE UNIT COMPLEMENT.
It does not yet characterize every stationary vector as a real scalar
multiple of U; general completed linear/centering operations are still open.

## Nonzero excitation and same-object correlation pin

For each original presentation x, use its actual spatial mean
`mu=B_dense(x,unit)` and the literal rationally centered presentations
`x-mu.approx(n)*unit`. Their squared distance is exactly
`(mu.approx(m)-mu.approx(n))^2`. The scalar modulus at
`min(epsilon,1)` therefore gives a squared-distance Cauchy modulus without
a square root, choice, or an assumed completed real-scalar action.

The resulting vector v_x is orthogonal to U. At every fixed discrete lag n,

```text
B(v_x,T_n v_y) = class(spatialCenteredMoment(n,x,y)).
```

The right side is already pinned to the original common-action/partition
connected diagonal by `originalConnected_diagonal_converges` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialCenteredForm.lean:127`.
For the actual origin face, `origin_physical` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialCentralExcitation.lean:43`
supplies membership for every positive base. Its vector has
`B(v,v)>=starRatio(w)>0`, using `spatialCenteredFace_floor` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialDenseGap.lean:170`
and `starRatio_positive` at
`lean/YMGap/Continuum/BF4ExactSlabLocalStarComparison.lean:65`.
This is an actual nonzero vector in the same strict sector, not merely a
positive scalar determinant or a nonzero unit.

## Parameters and remaining frontier

Every analytic construction retains `0<w<1`, `base>0`,
`heatRatio(w)<=1/2`, `heatRemainderBound(w)<1`, and
`rho(w)=entropyRate 625 (adjustedCoreRate w hd)<1`. Rate and excitation
floor depend on coupling but not positive base size. The moduli and
representative ceilings retain their actual vector/base/coupling dependence.
There is no all-beta or lattice-spacing-uniform statement.

The present family consists of separate completions of fixed-base
presentations using spatial limiting states. It is not yet one completion
of all finite spatial supports. A Cauchy stream with unbounded support bases
cannot be placed in one of those fixed-base completions without a theorem.
The source-reviewed next route is a staged carrier paired at the explicit
maximum base, using `spatialPairing_inclusion` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBaseCoherence.lean:294`.
Extracting the pairing-completion argument over an existing SquaredSeminorm,
actual dense pairing and Type-valued approximation/continuity data should
avoid copying this proof tower again. This is a plan, not an implemented
generic theorem or a supplied union construction.

General completed linear/centering laws, metric completeness, full spatial
translation and observable-algebra pins, Hilbert/OS/QFT reconstruction,
physical time/spacing calibration, controlled continuum passage and
nontriviality, and the all-compact-simple-group target remain open. The
operator here is actual discrete physical time of the reflected lattice
form, not heat-bath dynamics; no continuum Hamiltonian or spectral
identification is constructed by this checkpoint.

## Verification boundary

Twelve focused serialized one-worker/20 GiB checks passed through the
monitored launcher. All 110 printed public gates were within
`{propext, Quot.sound}`: 103 in eleven new modules and 7 in the modified
existing helper module. Final logs contain no errors, warnings, sorryAx,
classical dependency or native-reduction axiom. One missing explicit
parameter binding in the new margin-positivity theorem was corrected and
rechecked; the failed attempt is not counted as verification.

Independent source review checked actual quotient/form/time identities,
Type-valued moduli, centering limits, positive-margin cancellation, and
the nonzero excitation. No new sorry, axiom, analytic premise, weakened
canonical field or safety-limit change was introduced. No canonical
continuum scorecard closure is claimed.

Final local log hashes (SHA-256 of logs, not source files):

| Log under `/tmp/` | Gates | SHA-256 |
| --- | ---: | --- |
| `ym-spatial-pairing-bounds-20260916.log` | 8 | `da56db89cab818fe8e6fa8e90291dbc4d76bf6c1f09a71c5531412c6c3782c07` |
| `ym-spatial-pairing-continuity-20260916.log` | 3 | `414bf4ff2008c6ef2fb1e699c94e2f914df66877c531f082b4566f0223b514c4` |
| `ym-spatial-pairing-limit-20260916.log` | 13 | `a9011085f2cbaccb70ccacb514925448ee220e19f2647b8fd003b91360079dac` |
| `ym-spatial-completed-inner-20260916.log` | 12 | `b2b394f5056e6fa8af07d2b328accec74b7724d26aa17a120d731ae37f275937` |
| `ym-posdef-scalar-export-20260916.log` | 7 | `c53dfbcfd5163699960e41048c61c2de49fe1f05a1cfe281c331250a4f745aba` |
| `ym-spatial-completed-posdef-20260916.log` | 8 | `20e0f22e32620989f7424dd1af634053eb4cf6844708b2dd28505360471a0193` |
| `ym-spatial-center-algebra-20260916.log` | 7 | `b6b8fd25f7c230d9bb22ce826792e46b1ab4b6b8df91a5bdad808e87de81fc21` |
| `ym-spatial-centered-stream-20260916.log` | 8 | `314afe068b14b536decb716b223d438d87bd24dde96c3d40557db63cc1500b7a` |
| `ym-spatial-centered-pairing-20260916.log` | 6 | `372377d20137c85616e5a292627eca9043716d08f026f2c9b47b0e560cc39d3d` |
| `ym-spatial-completed-gap-20260916.log` | 11 | `ecf3a2b33739a0f2da0cc4e3282a8e8b7ae2268fcc8106977af73cf6254dc5a6` |
| `ym-spatial-unit-complement-20260916.log` | 17 | `98513d865e692f811afa0e8c4d36fb98a162274d9b0081206ac982aaa0d20055` |
| `ym-spatial-central-excitation-20260916.log` | 10 | `7c1b223948a75d7a8180f1827713b3263281b0d9eca2530bb38e2dda6f547dc2` |

Eleven root imports were added. Root/full-tree builds and the full audit
were not run. CI remains manual-only. No routine literature scan ran;
the cached math-ph review and minimum 12-hour interval remain in force.
