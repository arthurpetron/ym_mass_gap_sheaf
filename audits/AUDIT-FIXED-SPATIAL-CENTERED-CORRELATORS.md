# Original unit projection, centered time and common-partition correlations

Date: 2026-09-16. Classification: PROGRESS after `7a8bfc5`.

WHOLE-PROJECT GOAL: nontrivial continuum Yang--Mills on R^4, the required
QFT axioms and a positive physical Hamiltonian gap for every compact simple
group, on the SAME theory, within the constructive axiom gate. This result
concerns fixed-nome, fixed-width, fixed-cutoff SU(2) on the selected original
spatial-probe domain. The whole target remains open.

## Mathematical result

The actual fixed-unit projection and orthogonal centering are now constructed
on the existing original Cauchy carrier. Physical time commutes with centering
and restricts to the unit complement. Its centered pairing is exactly the
constructed limit of a literal finite connected expectation whose joint
moment and both unit-marginals have ONE common action and partition.

Expansion makes the scalar and vector moduli, the unit coefficient and the
common finite chart explicit. Contraction combines their proved estimates
into the projection, centered evolution and SAME-object connected limit.
No new analytic premise is assumed.

1. For scalar data `s, cs : QCauchy s.approx` and vector representative X,
   let A=abs(s.approx(cs.M 1))+1 and B=normCeiling(X). The exact scalar-change
   identity costs (a-b)^2*B(X,X). Split a*X_m-b*X_n through a*X_n.
   Each squared-distance leg receives epsilon/4 before the factor-two
   triangle. The rate is
   max(cs.M 1, normBase X, X.modulus((epsilon/4)/(A*A+1)),
   cs.M(min((epsilon/4)/(B+1),1))). It uses actual tail anchors, no scalar
   sign or positive-norm assumption, and no extracted legacy modulus.
2. Original pairing homogeneity passes through the same scalar limits.
   Positive definiteness separates vectors by their pairings and proves
   independence of scalar/vector representatives and of the supplied scalar
   modulus. The public operation still takes CReal WITH QCauchy data;
   it is not an unrestricted action of bare quotient reals.
3. The unit coefficient is representativeInner(X,constant unit), with its
   already constructed representativeInnerCauchy witness. Scaling the
   constant unit stream constructs P(X). Pairing separation descends P to
   the quotient without representative selection. Its pairing is
   B(Px,y)=B(x,u)*B(u,y). It is self-adjoint, idempotent, unit-preserving
   and norm-contractive.
4. C=I-P is self-adjoint, idempotent and linear for the constructed
   operations. It is unit-orthogonal and nonexpansive. The exact identity
   B(Cx,Cy)+B(Px,Py)=B(x,y) is a mixed Pythagorean decomposition, not an
   assumed norm comparison.
5. Actual time balance and T_n u=u give P*T_n=T_n*P=P and T_n*C=C*T_n.
   The restricted unitComplementTime has value exactly T_n x.val and
   inherits zero/add-time laws. Thus
   B(Cx,T_n Cy)=B(x,T_n y)-B(x,u)*B(u,y).
   Even-time positivity and constant-one contraction remain non-strict.
6. Fix H containing the two physical presentations. At depth t every
   chartScalar uses E=adjacentEvenExtent(width+t+H), start=width+1,
   chainIds E width start (t+(2*H+t)), the same retained stage and the same
   finiteValue partition. Only the signed insertion varies. Joint (x,y),
   left (x,u) and right (u,y) are therefore moments of one finite action,
   not moments from three separately minimized chart sizes.
7. Each raw chart stream has the existing windowTimeModulus with its
   actual mixed-polynomial cap. Generic scalar Cauchy arithmetic combines
   joint-left*right at the SAME raw index before ofQ'CauchySeq reindexing.
   The private rawReal helper merely packages approx:=raw stream and fills
   its propositional Cauchy field from the separately supplied Type data.
   All moduli remain available in connectedCauchy. Chart independence and
   product/subtraction continuity identify the result with the centered
   pairing. Replacing y by physicalTime n y pins the actual centered time
   correlator. Physical lag n is independent of receding boundary depth t.

## Declaration evidence

All table paths have prefix `lean/YMGap/Continuum/`.

| Declaration | Module:line | Role |
|---|---|---|
| `distSq_scalar_difference`, `realScalarRate`, `realScalar_bound`, `realScalarCauchy` | `BF4ExactSlabFixedSpatialRealScalarCauchy.lean:73`, `:116`, `:125`, `:188` | Actual scalar-change estimate and returned Cauchy data. |
| `completed_eq_of_pairings`, `realScalarCauchy_congr`, `completedRealSmul` | `BF4ExactSlabFixedSpatialCompletedRealScalar.lean:46`, `:75`, `:85` | Same-form separation and choice-free scalar descent. |
| `unitCoefficient`, `unitCoefficientCauchy`, `unitProjectionCauchy`, `unitProjection` | `BF4ExactSlabFixedSpatialUnitProjection.lean:63`, `:67`, `:76`, `:95` | Computed coefficient, explicit modulus and original projection. |
| `unitProjection_pairing`, `unitProjection_idempotent`, `unitProjection_norm_le` | `BF4ExactSlabFixedSpatialUnitProjection.lean:104`, `:120`, `:167` | Actual projection laws. |
| `center`, `centerCauchy`, `center_orthogonal`, `centered_inner` | `BF4ExactSlabFixedSpatialCenteredCompletion.lean:83`, `:86`, `:103`, `:158` | Actual centering and connected pairing. |
| `orthogonal_decomposition_inner`, `center_nonexpansive`, `UnitComplement` | `BF4ExactSlabFixedSpatialCenteredCompletion.lean:163`, `:174`, `:181` | Exact geometry and unit-orthogonal subtype. |
| `completedTime_center`, `unitComplementTime`, `unitComplementTime_val`, `centered_time_pairing` | `BF4ExactSlabFixedSpatialCenteredPhysicalTime.lean:83`, `:90`, `:94`, `:116` | SAME physical evolution and connected-time identity. |
| `centered_even_nonnegative`, `centered_even_le_identity`, `centered_time_norm_le` | `BF4ExactSlabFixedSpatialCenteredPhysicalTime.lean:122`, `:127`, `:133` | Even positivity and constant-one bounds only. |
| `chartScalar`, `chartScalar_pin`, `chartCauchy`, `chartScalar_converges` | `BF4ExactSlabFixedSpatialCommonChartCorrelator.lean:61`, `:72`, `:102`, `:131` | Common finite action, actual window pin, rate and intrinsic limit. |
| `connectedScalar`, `connectedCauchy`, `connectedLimit`, `connectedLimit_pin` | `BF4ExactSlabFixedSpatialOriginalConnectedCorrelator.lean:71`, `:78`, `:86`, `:103` | Literal same-index covariance and constructed limit. |
| `centered_originalCorrelator`, `centeredTime_originalCorrelator` | `BF4ExactSlabFixedSpatialOriginalConnectedCorrelator.lean:115`, `:126` | SAME-partition connected limit equals actual centered form/time pairing. |

## Next causal frontier and remaining boundaries

The next producer is an exact separated-window contraction/factorization
identity and a normalized covariance bound in the separation. It is NOT
provided by this checkpoint. Existing reusable inputs are:

- `lean/YMGap/Continuum/SU2QuaternionHeadWindowContraction.lean:201`,
  `windowMessage_iterate`: whole-window contraction is an actual algebraic
  iterate, including observables depending on later slices.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowBracket.lean:88`,
  `windowBracket_width`: actual observed-message bracket width is 2*C*q^g.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowInput.lean:201`,
  `inputNumerator_abs_le`: a signed window tested against a certified input
  is bounded without requiring positive residual mass.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferMixingRate.lean:110`,
  `mixRate`, with `mixRate_nonnegative` at `:113` and `mixRate_lt_one` at
  `:124`: q depends on nome and width, not late cutoff. It may equal zero.

The two-window argument must preserve the common unobserved partition and
must not divide by signed insertion mass or a possibly zero residual mass.
`windowRatio_right_commonTail` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowBracket.lean:140`
controls boundary forgetting for a fixed insertion; it is not already a
physical-separation covariance theorem. The subsequent reflected-norm
upgrade and completed strict bound remain separate proof obligations.

The scalar-stream ceilings depend on supplied representatives/moduli.
The raw chart modulus is inherited exactly, but multiplication's computed
tail ceilings can depend on the actual finite scalar values; no new joint
cutoff-uniform connected modulus is claimed. No width/spacing-uniform
strict rate or physical mass calibration is asserted.

The fixed unit need not yet be the entire fixed-point space. Nonconstant
excitations, vacuum uniqueness/isolation, strict gap, metric completeness,
full gauge algebra and Hilbert/OS reconstruction, joint cutoff/time and
spatial/spacing passage, continuum QFT and the all-group Clay target remain
open. No canonical field, literal hole, axiom or analytic premise changed.

## Focused verification

Seven modules passed focused monitored checks, serialized with one worker
and a 20 GiB hard ceiling. Each had fresh process/swap preflight. All 97
public gates stay within {propext, Quot.sound}. Final logs have no errors,
warnings, sorryAx or classical dependencies. The connected-limit proof's
initial elaboration timeouts were repaired with explicitly typed generic
limit arithmetic and termwise equivalence; statements and resource limits
were unchanged. Root/full-tree/full axiom audit were not run. Seven imports
were added to the selective root, without a root-build claim.

| Module suffix | Gates | `/tmp/<full module name>.log` SHA-256 |
|---|---:|---|
| `RealScalarCauchy` | 8 | `3b74f59c3375a243ee7669ac0c3f23e879a1bc23f966735c461bb8ac794fc22c` |
| `CompletedRealScalar` | 14 | `fd5f61b0d384d0c888cd6d55efd79cb5e699a7ce3b7a4fd4c3807edfd14d1d89` |
| `UnitProjection` | 19 | `bf45c6d73b94dbb34e37a53ec2ed1546bf743070b12121e39c661ec3d5dee3ac` |
| `CenteredCompletion` | 28 | `79f70de4d057e1ddbe93b8dca98830b3dba9f7345d6bee5369721c3d966712de` |
| `CenteredPhysicalTime` | 15 | `7623cffed3b064e3b56de7ecd5a88a6326ea3ff6e1abd7152f68ab724ec972e6` |
| `CommonChartCorrelator` | 6 | `acda0b03efbecfc84ec45f3725e1e5a49be064399df2b2fcdacd649fce70a999` |
| `OriginalConnectedCorrelator` | 7 | `67463039817bedfe691652258243d1048154ea4455a1e919f0ff7a86d13df6f4` |

Each suffix has prefix BF4ExactSlabFixedSpatial. Independent source review
checked both epsilon/4 budgets, retained coefficient modulus, no-choice
projection, exact centering geometry, common finite partition and literal
physical-time restriction. Parallel agents worked on disjoint files/reviews;
only the main agent compiled. CI and capacity limits are unchanged. No
literature scan was performed; the 12-hour review cadence remains in force.
