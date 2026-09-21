/-
# Ceilings for the computed fixed-spatial response witnesses

The explicit one-step witness is at most `1/5`, and the explicit two-step
witness is at most `1/25`.  These are upper bounds on the particular LOWER
BOUND NUMBERS constructed by the dual-test argument.  They are not upper
bounds on the actual response, on a Rayleigh quotient, or on the transfer
operator.  In particular they cannot refute physical survival; they only show
that iterating this coarse witness cannot itself provide a near-one Rayleigh
certificate.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteTwoStepResponse
import YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound
import YMGap.Continuum.PhysicalSeparatorLinearTail

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialResponseFloorCeiling

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
  (headFloor headFloor_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
  (kineticFloor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDualCost
  (inverseRate costCap costCap_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialResponseMassBounds
  (detectorScale partitionScale)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteUniformResponse
  (uniformFloor uniformFloor_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteTwoStepResponse
  (normCeiling normCeiling_positive twoStepFloor relativeFloor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalCovariance
  (separationCap separationCap_nonnegative)
open YMGap.Continuum.BF4ExactSlabSharedWindowFloorBound
  (headFloor_le_oneThirtySecond)
open YMGap.Continuum.PhysicalSeparatorLogRate (PhysicalSpacing)
open YMGap.Continuum.PhysicalSeparatorLinearTail (SpacingToZero)

private theorem headFloor_le_one {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    headFloor w ≤ (1 : Q') :=
  Q'.le_trans' _ _ _ (headFloor_le_oneThirtySecond hw0 hw1) (by decide)

private theorem detectorScale_le_one {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat) :
    detectorScale w width ≤ (1 : Q') := by
  have hh0 : (0 : Q') ≤ headFloor w := Q'.le_of_lt (headFloor_positive hw0 hw1)
  have ht := HKPos.pow_le_one hh0 (headFloor_le_one hw0 hw1)
    (BF4ExactSlabFixedSpatialFacePlacement.temporalFaces width).length
  have hs := HKPos.pow_le_one hh0 (headFloor_le_one hw0 hw1)
    (spatialFaces width).length
  unfold detectorScale kineticFloor
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg ht hs (by decide : (0 : Q') ≤ 1)
      (Q'.pow_nonneg _ hh0 _))
    (Q'.le_of_eqv (Q'.mul_one_eqv 1))

private theorem costCap_ge_five {w : Q'} (hw0 : (0 : Q') < w) :
    (5 : Q') ≤ costCap hw0 := by
  have hi : (0 : Q') ≤ inverseRate hw0 := by
    unfold inverseRate
    exact Q'.le_of_lt (Q'.recipPos_pos _ _)
  unfold costCap
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 5 _ hi)
    (Q'.le_of_eqv (Q'.add_comm_eqv 5 _))

private theorem partitionScale_ge_one {w : Q'} (hw0 : (0 : Q') < w)
    (width : Nat) : (1 : Q') ≤ partitionScale w width := by
  unfold partitionScale
  exact Q'.add_le_self_of_nonneg 1 _
    (Q'.mul_nonneg _ _
      (BF4ExactSlabFixedSpatialTransferSandwich.kineticCap_nonnegative hw0 width)
      (SumOfSquares.q_mul_self_nonneg _))

/-- The particular cutoff/depth-uniform lower witness is never larger than
`1/5`.  This says nothing about an upper bound for the response it witnesses. -/
theorem uniformFloor_le_oneFifth {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat) :
    uniformFloor hw0 width ≤ Q'.mkPos 1 5 (by decide) := by
  let A := detectorScale w width
  let D := costCap hw0 * partitionScale w width
  have hA0 : (0 : Q') ≤ A :=
    Q'.le_of_lt
      (BF4ExactSlabFixedSpatialResponseMassBounds.detectorScale_positive hw0 hw1 width)
  have hA : A ≤ (1 : Q') := detectorScale_le_one hw0 hw1 width
  have hnum : A*A ≤ (1 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg hA hA (by decide : (0 : Q') ≤ 1) hA0)
      (Q'.le_of_eqv (Q'.mul_one_eqv 1))
  have hDpos : (0 : Q') < D :=
    Q'.mul_pos (costCap_positive hw0)
      (BF4ExactSlabFixedSpatialResponseMassBounds.partitionScale_positive hw0 width)
  have hD : (5 : Q') ≤ D :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.mul_one_eqv 5))
      (Q'.mul_le_mul_of_nonneg (costCap_ge_five hw0)
        (partitionScale_ge_one hw0 width)
        (Q'.le_of_lt (costCap_positive hw0)) (by decide : (0 : Q') ≤ 1))
  have hone : (1 : Q') ≤ Q'.mkPos 1 5 (by decide) * D :=
    Q'.le_trans' _ _ _ (by decide : (1 : Q') ≤ Q'.mkPos 1 5 (by decide) * 5)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hD (by decide))
  change Q'.divPos (A*A) D hDpos ≤ Q'.mkPos 1 5 (by decide)
  exact Q'.divPos_le_of_le_mul (A*A) D hDpos
    (Q'.le_trans' _ _ _ hnum hone)

/-- Squaring the preceding witness and paying the positive norm ceiling gives
an explicit two-step witness at most `1/25`.  Again, the actual two-step
response may be larger. -/
theorem twoStepFloor_le_oneTwentyFifth {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width) :
    twoStepFloor hw0 width face hf ≤ Q'.mkPos 1 25 (by decide) := by
  let d := uniformFloor hw0 width
  let P := normCeiling width face hf
  have hd0 : (0 : Q') ≤ d := Q'.le_of_lt (uniformFloor_positive hw0 hw1 width)
  have hd : d ≤ Q'.mkPos 1 5 (by decide) :=
    uniformFloor_le_oneFifth hw0 hw1 width
  have hsq : d*d ≤ Q'.mkPos 1 25 (by decide) :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg hd hd (by decide) hd0)
      (by decide)
  have hPpos : (0 : Q') < P := normCeiling_positive width face hf
  have hP : (1 : Q') ≤ P := by
    unfold P normCeiling
    exact Q'.add_le_self_of_nonneg 1 _
      (separationCap_nonnegative width
        (BF4ExactSlabFixedSpatialFaceCharacter.faceSpan width face hf).val
        (BF4ExactSlabFixedSpatialFaceCharacter.faceSpan width face hf).val)
  have hscaled : Q'.mkPos 1 25 (by decide) ≤
      Q'.mkPos 1 25 (by decide) * P :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hP (by decide))
  change Q'.divPos (d*d) P hPpos ≤ Q'.mkPos 1 25 (by decide)
  exact Q'.divPos_le_of_le_mul (d*d) P hPpos
    (Q'.le_trans' _ _ _ hsq hscaled)

/-- The further homogeneous lower witness is also at most `1/25`.  This is
still only a ceiling on the chosen witness coefficient, not on the actual
Rayleigh quotient that the coefficient bounds from below. -/
theorem relativeFloor_le_oneTwentyFifth {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width) :
    relativeFloor hw0 width face hf ≤ Q'.mkPos 1 25 (by decide) := by
  let d₂ := twoStepFloor hw0 width face hf
  let P := normCeiling width face hf
  have hd₂ : d₂ ≤ Q'.mkPos 1 25 (by decide) :=
    twoStepFloor_le_oneTwentyFifth hw0 hw1 width face hf
  have hPpos : (0 : Q') < P := normCeiling_positive width face hf
  have hP : (1 : Q') ≤ P := by
    unfold P normCeiling
    exact Q'.add_le_self_of_nonneg 1 _
      (separationCap_nonnegative width
        (BF4ExactSlabFixedSpatialFaceCharacter.faceSpan width face hf).val
        (BF4ExactSlabFixedSpatialFaceCharacter.faceSpan width face hf).val)
  have hscaled : Q'.mkPos 1 25 (by decide) ≤
      Q'.mkPos 1 25 (by decide) * P :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hP (by decide))
  change Q'.divPos d₂ P hPpos ≤ Q'.mkPos 1 25 (by decide)
  exact Q'.divPos_le_of_le_mul d₂ P hPpos
    (Q'.le_trans' _ _ _ hd₂ hscaled)

/-- The defect of THIS witness stays at least 24/25. This is not a lower
bound on the defect of the actual operator or the actual Rayleigh quotient. -/
theorem relativeFloor_defect_ge {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width) :
    Q'.mkPos 24 25 (by decide) ≤ 1 + -(relativeFloor hw0 width face hf) :=
  Q'.le_trans' _ _ _
    (by decide : Q'.mkPos 24 25 (by decide) ≤ 1 + -(Q'.mkPos 1 25 (by decide)))
    (Q'.add_le_add (Q'.le_refl' 1)
      (Q'.neg_le_neg (relativeFloor_le_oneTwentyFifth hw0 hw1 width face hf)))

/-- An explicit scale refutes a linear-spacing defect bound for this coarse
lower witness, even if nome, width and face are chosen anew at every scale.
No conclusion about actual Yang--Mills scaling or survival follows. -/
theorem relativeFloor_no_linear_defect {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (A : PhysicalSpacing) (Z : SpacingToZero A) (M : Q') (hM : (0 : Q') < M)
    (j : Nat) (hj : Z.modulus (Q'.divPos HalfPow.half M hM) ≤ j) :
    ¬ (1 + -(relativeFloor hw0 width face hf) ≤ M * A.spacing j) := by
  intro hdef
  have ha := Z.spacing_le (Q'.divPos HalfPow.half M hM)
    (Q'.divPos_pos _ _ _ (by decide : (0 : Q') < HalfPow.half)) j hj
  have hsmall : M * A.spacing j ≤ HalfPow.half :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ M ha (Q'.le_of_lt hM))
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
        (Q'.divPos_mul_eqv HalfPow.half M hM)))
  exact (by decide : ¬ (Q'.mkPos 24 25 (by decide) ≤ HalfPow.half))
    (Q'.le_trans' _ _ _ (relativeFloor_defect_ge hw0 hw1 width face hf)
      (Q'.le_trans' _ _ _ hdef hsmall))

end YMGap.Continuum.BF4ExactSlabFixedSpatialResponseFloorCeiling

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialResponseFloorCeiling.uniformFloor_le_oneFifth
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialResponseFloorCeiling.twoStepFloor_le_oneTwentyFifth
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialResponseFloorCeiling.relativeFloor_le_oneTwentyFifth
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialResponseFloorCeiling.relativeFloor_defect_ge
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialResponseFloorCeiling.relativeFloor_no_linear_defect
