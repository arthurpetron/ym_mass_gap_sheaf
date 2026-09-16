/-
# The shrinking transfer bracket bounds the original normalized chain scalar

The V-weighted mass of the actual source-probe iterate is the pre-existing
compact numerator with an empty terminal probe. The corresponding iterate
of one is the SAME compact partition. Both reciprocal constructions cancel
this one denominator, so their normalized rational values agree exactly.

The existing geometry and face-membership pins then place the original
selected-action finiteValue in the computed sourceProbeBracket. The terminal
spatial weight is retained, including at zero steps. The bracket centre may
depend on time and cutoff: no stationary state, connected-correlation bound,
OS identification or continuum limit is asserted here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketDecay
import YMGap.Continuum.BF4ExactSlabFixedSpatialIterationLimit

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketOriginalScalar

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabTemporalSweep (FaceFactor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry (chainIds chainIds_physical)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass (weightedMass_one_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket (massRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketDecay
open YMGap.Continuum.BF4ExactSlabFixedSpatialIterationLimit
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal (reciprocalTerm)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

/-- The terminal V is the same factor; only commutativity and the empty
terminal probe's unit are used. No physical-face premise is needed. -/
theorem weightedMass_iterate_compactNumerator (w : Q') (K width steps : Nat)
    (fs : List FaceFactor) :
    weightedMass w K width
        (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) steps
          (sourceProbe width fs)) ≈
      compactNumerator w K width steps fs [] := by
  let f := iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) steps
    (sourceProbe width fs)
  change quaternionHaar (N width) (polyMul (spatialWeight w K width) f) ≈
    quaternionHaar (N width) (polyMul f (polyMul (spatialWeight w K width) polyOne))
  exact haar_of_coeff ((RatPolyCoeffEqv.mul_comm _ _).trans
    ((RatPolyCoeffEqv.refl f).mul (RatPolyCoeffEqv.mul_one (spatialWeight w K width)).symm))

/-- The denominator is exactly the original compact empty/empty partition. -/
theorem weightedMass_iterate_compactPartition (w : Q') (K width steps : Nat) :
    weightedMass w K width
        (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) steps polyOne) ≈
      compactPartition w K width steps :=
  weightedMass_iterate_compactNumerator w K width steps []

private theorem reciprocal_unique (z r s : Q') (hr : z*r ≈ 1) (hs : z*s ≈ 1) : r ≈ s :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_one_eqv r))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left r _ _ (Q'.eqv_symm hs))
      (Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.mul (.var 1) (.var 0)) (.var 2)) (by decide)
          (fun | 0 => r | 1 => z | _ => s))
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ s hr) (Q'.one_mul_eqv s))))

/-- The bracketed ratio uses the SAME reciprocal normalization as the existing
compact scalar stream. Geometry is needed for the partition reciprocal pin,
but no face validity is needed for this compact algebraic equality. -/
theorem sourceProbeMassRatio_normalizedScalar {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width start steps extent : Nat} (hw : width ≤ extent) (ht : start+steps ≤ extent)
    (fs : List FaceFactor) (stage : Nat) :
    sourceProbeMassRatio hw0 hw1 (headCutoff w+stage) width
        (Nat.le_add_right _ _) steps fs ≈
      normalizedScalar w hw0 hw1 extent width start steps fs [] stage := by
  let K := headCutoff w+stage
  let g := iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) steps polyOne
  have hg : (0 : Q') < weightedMass w K width g :=
    iterateWeightedMass_positive hw0 hw1 K width (Nat.le_add_right _ _) steps
      (supported_one (N width)) (Certificate.one (N width))
      (weightedMass_one_positive hw0 hw1 K width (Nat.le_add_right _ _))
  let z := weightedMass w K width g
  let r := Q'.recipPos z hg
  let s := reciprocalTerm w hw0 hw1 extent (chainIds extent width start steps)
    (fun _ hi => chainIds_physical hi) stage
  have hr : z*r ≈ 1 := Q'.mul_recipPos_eqv z hg
  have hs : z*s ≈ 1 :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ s (weightedMass_iterate_compactPartition w K width steps))
      (compactPartition_reciprocal w hw0 hw1 hw ht stage)
  have hrs : r ≈ s := reciprocal_unique z r s hr hs
  change weightedMass w K width
      (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) steps
        (sourceProbe width fs)) * r ≈ compactNumerator w K width steps fs [] * s
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ r (weightedMass_iterate_compactNumerator w K width steps fs))
    (Q'.mul_eqv_congr_left _ _ _ hrs)

/-- Physical face placement pins the ratio to the pre-existing original
selected-action normalized rational expectation, not a new scalar surrogate. -/
theorem sourceProbeMassRatio_originalFiniteValue {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width start steps extent : Nat} (hw : width ≤ extent) (ht : start+steps ≤ extent)
    (fs : List FaceFactor) (hfs : ∀ f, f ∈ fs → f.1 ∈ spatialFaces width) (stage : Nat) :
    sourceProbeMassRatio hw0 hw1 (headCutoff w+stage) width
        (Nat.le_add_right _ _) steps fs ≈
      finiteValue w hw0 hw1 extent (chainIds extent width start steps)
        (fun _ hi => chainIds_physical hi) (endpointInsertion extent start steps fs []) stage :=
  Q'.eqv_trans _ _ _ (sourceProbeMassRatio_normalizedScalar hw0 hw1 hw ht fs stage)
    (normalizedScalar_pin w hw0 hw1 hw ht fs [] hfs
      (fun _ hm => False.elim (List.not_mem_nil hm)) stage)

/-- The original finite-chain scalar lies in the actual constructed bracket,
whose width is the already proved q^steps * (probeCap+probeCap). -/
theorem originalFiniteValue_bounds {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width start steps extent : Nat} (hw : width ≤ extent) (ht : start+steps ≤ extent)
    (fs : List FaceFactor) (hfs : ∀ f, f ∈ fs → f.1 ∈ spatialFaces width) (stage : Nat) :
    (sourceProbeBracket hw0 hw1 (headCutoff w+stage) width
        (Nat.le_add_right _ _) steps fs).lower ≤
        finiteValue w hw0 hw1 extent (chainIds extent width start steps)
          (fun _ hi => chainIds_physical hi) (endpointInsertion extent start steps fs []) stage ∧
      finiteValue w hw0 hw1 extent (chainIds extent width start steps)
          (fun _ hi => chainIds_physical hi) (endpointInsertion extent start steps fs []) stage ≤
        (sourceProbeBracket hw0 hw1 (headCutoff w+stage) width
          (Nat.le_add_right _ _) steps fs).upper := by
  have he := sourceProbeMassRatio_originalFiniteValue hw0 hw1 hw ht fs hfs stage
  have hb := sourceProbeMassRatio_bounds hw0 hw1 (headCutoff w+stage) width
    (Nat.le_add_right _ _) steps fs
  exact ⟨Q'.le_trans' _ _ _ hb.1 (Q'.le_of_eqv he),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv he) hb.2⟩

end YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketOriginalScalar

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketOriginalScalar.weightedMass_iterate_compactNumerator
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketOriginalScalar.weightedMass_iterate_compactPartition
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketOriginalScalar.sourceProbeMassRatio_normalizedScalar
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketOriginalScalar.sourceProbeMassRatio_originalFiniteValue
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracketOriginalScalar.originalFiniteValue_bounds
