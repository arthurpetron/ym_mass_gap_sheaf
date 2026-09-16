# Parallel frontier: every compact simple group

Source audit, 2026-09-16. No Lean file was changed or compiled by this reviewer.
Existing declarations were inspected; this report does not claim a new kernel
verification of them. Its consumer is selection of independent work ahead of
the current SU(2) same-carrier analysis, not another frontier bundle.

## Outcome

The all-group branch can advance independently of the completed SU(2) strict
bound at three upstream seams: global-form realization/descent, representation
and heat-tail data, and an original-action positive functional for a second
group. Their physical assembly is not supplied by the existing all-simple-type
composition theorem. The reusable completion machinery is already a fourth,
shared branch; it should not be duplicated per group.

The present strict bound is already a declaration on the actual SU(2) union
completion: `BF4SpatialUnionCompletedGap.completed_twoStep_form_gap`,
`lean/YMGap/Continuum/BF4SpatialUnionCompletedGap.lean:153`. It assumes the
explicit small-nome guards and unit orthogonality, and uses the actual
`completedTime 2`. It does not quantify over a gauge-group parameter. The
same module's `representative_twoStep_form_gap` at line 98 obtains its input
from the SU(2) dense centered estimate, not from `AllSimpleTypes`.

## Existing independent work and precise residuals

| Branch | Existing source-backed output | Residual before physical use | Depends on the current SU(2) strict proof? |
|---|---|---|---|
| Global forms | `CompactSimpleGlobalFormCode`, `lean/YMGap/RepTheory/CompactSimpleGlobalForm.lean:318`; `simplyConnectedCenter`, same file:93; `CenterSubgroupCode.order_mul_index`, same file:240 | Realize the marked code as the intended compact group and its central quotient, with topology/compactness, faithful action and a link to the lattice model. The code's fields contain none of these. | No. |
| Constructive quotient and representation descent | `CentralQuotientPresentation`, `lean/YMGap/RepTheory/ConstructiveGroup.lean:200`; `descendRepresentation`, `lean/YMGap/RepTheory/ConstructiveRepresentationDescent.lean:230`; `descendFaithful_of_kernelGammaWitness`, same file:315 | Supply the actual cover/quotient groups, finite central subgroup, Type-valued lift and exact-kernel witnesses; supply a matrix/unitary target and continuity. The existing descent is algebraic. | No. |
| Representation and heat-tail data | `SU3.casimir_split_le`, `lean/YMGap/RepTheory/SU3.lean:69`; `SU3.dimSq_le`, same file:116; `SU3CharFactor.charSum_le`, `lean/YMGap/Constructive/SU3CharFactor.lean:827`; `suN_C2_fundweight_gap_lb`, `lean/YMGap/RG/SUNWeylData.lean:89` | Relate these exact formulas to the actual representation objects and allowed global-form labels, then to the same group's Haar/heat functional and lattice action. The scalar inequalities alone supply no transfer operator. | No. |
| Actual positive functional and physical carrier for another group | The generic destination exists: `CanonicalOSRoot.WilsonFunctionalRoot`, `lean/YMGap/Continuum/CanonicalOSRoot.lean:53`, and `ReferenceWeightStageFamily`, same file:84 | A concrete non-SU(2) original-action realization feeding these fields and the same-carrier completion is **NOT FOUND** in the searched modules listed below. Generic reference weights do not identify a Wilson action or a group. | No dependence on finishing the SU(2) strict proof; does depend on that group's missing data. |
| Shared completion/analysis | `SquaredSeminorm`, `lean/YMGap/Continuum/CRealSeminormCompletion.lean:39`; `PairingData`, `lean/YMGap/Continuum/CRealSeminormPairingCompletionBounds.lean:33`; `completedInner`, `lean/YMGap/Continuum/CRealSeminormPairingCompletion.lean:78`; `Nonexpansive.completionMap`, `lean/YMGap/Continuum/CRealSeminormCompletion.lean:323` | Supply the chosen group's actual distance, dense pairing, QCauchy data, continuity estimates and actual transfer nonexpansiveness. These generic types have no group or Casimir field. | No. Reuse the same generic results once inputs are supplied. |

The exact current SU(2) input assembly is
`BF4SpatialUnionPairingData.pairingData`,
`lean/YMGap/Continuum/BF4SpatialUnionPairingData.lean:101`; its quantitative
fields are proved from the actual spatial pairing in a common base. This is
the integration seam for the shared completion machinery, not an all-group
instance.

The concurrent shared-analysis increment also now exists in the inspected
source: `CRealSeminormCompletedApproximation.DistanceData`,
`lean/YMGap/Continuum/CRealSeminormCompletedApproximation.lean:30`, has no
completeness assumption; `CRealSeminormCauchyRows.CauchyRows`,
`lean/YMGap/Continuum/CRealSeminormCauchyRows.lean:50`, carries the row
representatives and their outer modulus as data; `diagonalCauchy`, same
file:98, and `rowLimit`, same file:103, compute the limit, with
`rowLimit_independent`, same file:157, proving representation independence.
These declarations do not choose representatives for arbitrary quotient-valued
sequences. The actual SU(2) consumers are
`BF4SpatialUnionCauchyRows.rowLimit_time`,
`lean/YMGap/Continuum/BF4SpatialUnionCauchyRows.lean:69`,
`rowLimit_center`, same file:93, `rowLimit_orthogonal`, same file:102, and
`relaxationRows_limit`, same file:132. Their group-specific inputs remain the
existing physical SU(2) ones; the generic diagonal construction is reusable
without a separate all-group wrapper. The parent verifier owns the current
check evidence for this concurrent increment.

## Concrete checks that prevent false all-group progress

### 1. A Cartan scalar row is not a gauge group

`AllSimpleTypes.repOfCasimir`,
`lean/YMGap/MassGap/AllSimpleTypes.lean:106`, stores two Casimir scalars and a
fixed numerical operating point. `repDataOf`, same file:159, selects these
rows by Cartan code. `admissible_of_cartanType`, same file:183, proves the
legacy scalar floors and closure certificate, not a group realization.

The representative majorant explicitly has `rank := 1`:
`repOfCasimir_ztMajorant`,
`lean/YMGap/MassGap/AllSimpleTypes.lean:219`. Its being usable at every Cartan
code is not a derivation of every group's physical character expansion.

`mass_gap_of_cartanType`,
`lean/YMGap/MassGap/AllSimpleTypes.lean:280`, takes both `OSReconstruction
μ_inf` and `OSAxiomBundle μ_inf` as arguments. Those arguments have no type-level
dependence on the selected Cartan code. Thus the declaration does not construct
or identify that group's continuum theory. `PinnedSimpleLieType`,
`lean/YMGap/Rubric/ClayResolutionRoot.lean:38`, improves the scalar-row pin but
still has only Cartan-code, `RepData`, equality and admissibility fields.

### 2. Global form already changes the available observable

`so3_spinHalf_rejected`,
`lean/YMGap/RepTheory/CompactSimpleGlobalForm.lean:443`, constructively rejects
the doubled-spin label `1` for the SO(3) code;
`so3_spinOne_accepted`, same file:451, accepts label `2`.

The current actual excitation uses label `1`:
`BF4ExactSlabFixedSpatialFaceCharacter.faceCharacter`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFaceCharacter.lean:52`, is
`characterPolynomial ... 1`; `facePresentation`, same file:56, encodes that
same label; `BF4SpatialUnionExcitation.centralStage`,
`lean/YMGap/Continuum/BF4SpatialUnionExcitation.lean:43`, uses this face span.
Consequently an unchanged label-level reuse fails even for the other A1
global form. This is a source comparison with an existing proved rejection,
not a new theorem identifying an SO(3) representation or Haar functional.

### 3. A rational/finite algebraic fixture is not compact-group realization

`RationalQuaternion.UnitNorm.group`,
`lean/YMGap/RepTheory/RationalQuaternionUnitNormGroup.lean:419`, has rational
unit quaternions as carrier. Its module explicitly withholds compactness and
identification with all SU(2).

`RationalQuaternionBasisUnit.signLocatedQuotientPresentation`,
`lean/YMGap/RepTheory/RationalQuaternionQ8Fixture.lean:260`, instantiates the
located quotient construction for eight basis units modulo their two scalar
signs. The definition does not claim SO(3). The general constructive locator
consumer is `FiniteCentralSubgroup.locatedCentralQuotientPresentation`,
`lean/YMGap/RepTheory/LocatedCentralQuotient.lean:435`; its usable central-kernel
witness comes from supplied locator data, not a choice of quotient lifts.

### 4. Legacy Casimir floors must not be promoted to spectral minima

`soOdd_C2_fund`, `lean/YMGap/RepTheory/CasimirData.lean:75`, stores `n`;
`soEven_C2_fund`, same file:88, stores `(2n-1)/4`. Their documented meanings are
legacy scalar rows. `soOdd_gap_lb`, same file:100, and `soEven_gap_lb`, same
file:170, prove comparisons with `3/4`, not minimality among representations.

The module header at lines 29–35 records the B2/B3 spinor comparison and the
D-type normalization mismatch. A declaration deriving those spinor Casimirs
from actual highest-weight representations was **NOT FOUND** in
`RepTheory/CasimirData.lean`, `RepTheory/SimpleGroup.lean`,
`RepTheory/CompactSimpleGlobalForm.lean`, `RepTheory/CartanType.lean`,
`RG/SUNWeylData.lean`, `RG/WeylDimGeneral.lean` or
`MassGap/AllSimpleTypes.lean`. The prose warning is not reported as a new
checked representation-theory counterexample.

## What can be assigned now without duplicating the current proof

These are bounded work selections, not claims that their missing outputs
already exist:

1. **One global-form instance.** Exercise the existing
   `CentralQuotientPresentation` and `descendRepresentation` consumers on the
   intended compact group, retaining actual continuity/Haar obligations. The
   SO(3) label rejection above is an immediate test that the SU(2) fundamental
   excitation must not be passed through unchanged. The present finite fixture
   is already sufficient for testing the purely algebraic API; making another
   finite fixture would not remove this residual.
2. **One second-group analytic source.** SU(3) already has a nontrivial
   computed tail bound, `SU3CharFactor.charSum_le` at the declaration cited
   above, and its quantitative consumer `c_lf_su3_proven`,
   `lean/YMGap/Constructive/SU3CharFactor.lean:865`. The missing useful output is
   a pin to actual SU(3) character/Haar/action data, not another numerical
   `RepData` row.
3. **Keep shared analysis group-free.** The generic completion declarations
   above consume only actual quantitative algebraic data. Proving the same
   quotient-limit facts separately for every Cartan type would duplicate this
   existing consumer. Group-specific effort belongs in constructing its
   inputs and the physical dense strict estimate.

No new Lean module was introduced: every short algebraic wrapper considered
would only repackage an existing conditional consumer, whereas no bounded
physical non-SU(2) input was available to discharge. This is a source-backed
frontier audit and task selection, not closure of an all-group proof node.

## Search boundary / remaining all-group obligation

Searched `lean/YMGap/RepTheory/` in full by declarations and relevant source,
`MassGap/AllSimpleTypes.lean`, `MassGap/SimpleGroup.lean`,
`RG/SUNWeylData.lean`, `RG/WeylDimGeneral.lean`, `RG/WeylCharacterBound.lean`,
`Constructive/SU3CharFactor.lean`, `Continuum/CanonicalOSRoot.lean`,
`Continuum/ContinuumSelectedTheoryPins.lean`, the cited CReal completion and
BF4 spatial-union modules, and the Wilson/Haar module names and declarations
under `Continuum/`. No physically pinned non-SU(2) instance of the actual union
carrier/transfer/excitation was found in that scope.

`SelectedGroupUVPins`,
`lean/YMGap/Continuum/ContinuumSelectedTheoryPins.lean:120`, pins an inverse
coupling trajectory to the selected measure thread and a Cartan adjoint
Casimir. It does not supply the root/global-form/Haar construction. Neither
it nor the all-simple-type scalar theorem removes the unchanged requirement:
one physically identified, nontrivial continuum Yang–Mills theory with positive
physical Hamiltonian mass gap for **each compact simple global group**.
