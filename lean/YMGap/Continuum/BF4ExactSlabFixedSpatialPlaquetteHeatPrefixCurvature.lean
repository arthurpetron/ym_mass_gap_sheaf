/-
# Produced frozen curvature of the ORIGINAL spatial plaquette heat prefix

The literal face, selected physical edge, original cutoff and arbitrary
Haar insertions survive the Jacobi-to-character-prefix comparison. Its value,
three first and all nine ordered mixed errors are paid by an explicit
positive original head floor and a computed cutoff. Frozen supported
direction coefficients are never differentiated or magnitude-bounded.

At each fixed strict nome the cost is independent of width, face, cutoff
and direction. It is NOT uniform as nome tends to one, nor a completed
spatial-weight, conditional variance, OS, scaling or physical mass bound.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixJets
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteRadialCurvature
import YMGap.Continuum.QuaternionHaarFrozenCurvatureApproximation
import YMGap.Continuum.JacobiHeatPrefixCurvaturePrecision

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixCurvature

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported plaquette_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixJets
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteRadialCurvature
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPairedFrameAt (pairedDerivativeAt)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_add cap_mul_left)
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame (threeSquare)
open YMGap.Continuum.QuaternionHaarFrozenCurvatureApproximation (jetCurvature firstJet)
open YMGap.Continuum.QuaternionHaarThreePolynomialMatrixEnvelope (quadraticForm)
open YMGap.Continuum.JacobiHeatRadialProducedBound (nearFlatRadialCap nearFlatRadialCap_nonnegative)
open YMGap.Continuum.JacobiHeatPrefixCurvaturePrecision
  (nearFlatCurvatureCap nearFlatCurvatureCap_nonnegative nearFlatRadialOnset
    nearFlatRadialOnset_small_factor nearFlatRadialCap_le_curvatureCap)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
  (headFloor headFloor_positive headCutoff)

local notation:max "N" width:arg => List.length (baseLinks width)

def precisionFloor (w : Q') : Q' := HalfPow.half*(HalfPow.half*headFloor w)

/-- Chosen BEFORE the actual cutoff, with the produced original jet caps. -/
def plaquetteCurvatureTolerance (w : Q') : Q' :=
  JacobiHeatPrefixCurvaturePrecision.errorTolerance (precisionFloor w)
    (nearFlatCurvatureCap w) (prefixValueCap w) (prefixFirstCap w) (prefixSecondCap w)

def plaquetteCurvatureCutoff (w : Q') : Nat :=
  max (headCutoff w) (max (nearFlatRadialOnset w)
    (pairedDeficitCutoff w (plaquetteCurvatureTolerance w)))

/-- Same cost as the existing original relative heat, without an inverse-floor
or face-count factor. The strict nome dependence remains explicit. -/
def plaquetteCurvatureCost (w : Q') : Q' := nearFlatCurvatureCap w+1

def plaquettePrefixFrozenCurvature (width : Nat) (face : Z4Plaq) (l : Z4Link)
    (w C : Q') (K : Nat) (u : Fin 3 → RatPoly) : RatPoly :=
  let p := facePrefix w K width face
  let block := (baseLinks width).idxOf l
  jetCurvature C p (fun i => pairedDerivativeAt block i p)
    (fun i j => pairedDerivativeAt block i (pairedDerivativeAt block j p)) u

theorem precisionFloor_positive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (0 : Q') < precisionFloor w :=
  HKPos.q_mul_pos (by decide : (0 : Q') < HalfPow.half)
    (HKPos.q_mul_pos (by decide : (0 : Q') < HalfPow.half) (headFloor_positive hw0 hw1))

theorem plaquetteCurvatureTolerance_positive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (0 : Q') < plaquetteCurvatureTolerance w :=
  JacobiHeatPrefixCurvaturePrecision.errorTolerance_positive (precisionFloor_positive hw0 hw1)

private theorem six_quarter_square_le (m : Q') :
    6*((HalfPow.half*(HalfPow.half*m))*(HalfPow.half*(HalfPow.half*m))) ≤ m*m := by
  have hpin := poly_identity_of_normal_eq
    (.mul (.const 6)
      (.mul (.mul (.var 0) (.mul (.var 0) (.var 1)))
        (.mul (.var 0) (.mul (.var 0) (.var 1)))))
    (.mul (.mul (.const 6) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0))))
      (.mul (.var 1) (.var 1))) (by decide) (fun | 0 => HalfPow.half | _ => m)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ (m*m)
        (by decide : 6*((HalfPow.half*HalfPow.half)*(HalfPow.half*HalfPow.half)) ≤ (1 : Q'))
        (SumOfSquares.q_mul_self_nonneg m))
      (Q'.le_of_eqv (Q'.one_mul_eqv (m*m))))

/-- Full frozen matrix certificate for the SAME original finite character
prefix at every later computed cutoff. All nine actual mixed jets precede
multiplication by u; no sign, curvature or original-deficit input is assumed. -/
def plaquettePrefix_frozen_curvature_nearFlat_certificate
    {width : Nat} {face : Z4Plaq} {w : Q'}
    (hf : face ∈ spatialFaces width) (l : Z4Link) (hl : l ∈ edgesOf face)
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : plaquetteCurvatureCutoff w ≤ K) (u : Fin 3 → RatPoly)
    (hu : ∀ i, SupportedQuaternionBlocks (N width) (u i)) :
    Certificate (N width)
      (plaquettePrefixFrozenCurvature width face l w (plaquetteCurvatureCost w) K u) := by
  have hhead : headCutoff w ≤ K := by unfold plaquetteCurvatureCutoff at hK; omega
  have hradial : nearFlatRadialOnset w ≤ K+1 := by
    unfold plaquetteCurvatureCutoff at hK
    omega
  have herror : pairedDeficitCutoff w (plaquetteCurvatureTolerance w) ≤ K := by
    unfold plaquetteCurvatureCutoff at hK
    omega
  have ht : (0 : Q') < plaquetteCurvatureTolerance w :=
    plaquetteCurvatureTolerance_positive hw0 hw1
  let p := facePrefix w K width face
  let block := (baseLinks width).idxOf l
  let dp := fun i => pairedDerivativeAt block i p
  let ddp := fun i j => pairedDerivativeAt block i (pairedDerivativeAt block j p)
  let C := nearFlatRadialCap w (K+1)+1
  let Cbar := nearFlatCurvatureCap w
  have hC : (0 : Q') ≤ C :=
    Q'.zero_le_add _ _ (nearFlatRadialCap_nonnegative hw0 _) Q'.zero_le_one
  have hCCbar : C ≤ Cbar := nearFlatRadialCap_le_curvatureCap hw0 hw1 (K+1) hradial
  let P := prefix_value_interval (face := face) (Nat.le_refl (N width)) hw0 hw1 K
  let DP := prefix_first_interval hf hl (Nat.le_refl (N width)) hw0 hw1 K
  let DDP := prefix_mixed_interval hf hl (Nat.le_refl (N width)) hw0 hw1 K
  let E := deficit_value_interval (face := face) (Nat.le_refl (N width)) hw0 hw1 ht K herror
  let DE := deficit_first_interval hf hl (Nat.le_refl (N width)) hw0 hw1 ht K herror
  let DDE := deficit_mixed_interval hf hl (Nat.le_refl (N width)) hw0 hw1 ht K herror
  have hbudget : 6*QuaternionHaarCurvatureApproximation.errorCap C
      (prefixValueCap w) (prefixFirstCap w) (prefixSecondCap w)
      (plaquetteCurvatureTolerance w) (2*plaquetteCurvatureTolerance w)
      (4*plaquetteCurvatureTolerance w) ≤ headFloor w*headFloor w :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ 6
        (JacobiHeatPrefixCurvaturePrecision.error_budget (precisionFloor_positive hw0 hw1) hC
          (nearFlatCurvatureCap_nonnegative hw0) hCCbar
          P.nonnegative (DP 0).nonnegative (DDP 0 0).nonnegative) (by decide))
      (six_quarter_square_le (headFloor w))
  let floor := QuaternionHaarAllNomeHeatCertificate.prefixFloorCertificate hw0 hw1
    (plaquette_supported width (N width) (Nat.le_refl _) face)
    (plaquette_unit width (N width) (Nat.le_refl _) face) K hhead
  let weighted : Certificate (N width)
      (jetCurvature C (faceJacobi w (K+1) width face)
        (fun i => pairedDerivativeAt block i (faceJacobi w (K+1) width face))
        (fun i j => pairedDerivativeAt block i
          (pairedDerivativeAt block j (faceJacobi w (K+1) width face))) u) :=
    plaquetteJacobi_frozen_curvature_nearFlat_certificate hf l hl hw0 hw1 (K+1) (by omega)
      (nearFlatRadialOnset_small_factor hw0 hw1 (K+1) hradial) (by decide : (0 : Q') < 1) u hu
  let V : Certificate (N width) (jetCurvature (C+1) p dp ddp u) :=
    QuaternionHaarFrozenCurvatureApproximation.curvature_approximation_certificate u hu
      hC (Q'.le_of_lt (headFloor_positive hw0 hw1)) (prefix_split_pin hw0 hw1 K width face)
      (prefix_first_split_pin hw0 hw1 K width face block)
      (prefix_mixed_split_pin hw0 hw1 K width face block)
      P E DP DE DDP DDE hbudget floor weighted
  let direction : Certificate (N width) (threeSquare u) :=
    (Certificate.square (u 0) (hu 0)).add
      ((Certificate.square (u 1) (hu 1)).add (Certificate.square (u 2) (hu 2)))
  let S := Certificate.ofCoeff (cap_mul_left (Cbar + -C) (polyMul (threeSquare u) (polyMul p p)))
    (Certificate.smul (Cbar + -C) (Q'.sub_nonneg_of_le hCCbar)
      (direction.mul (Certificate.square p P.support)))
  have hcap : RatPolyCoeffEqv (cap (Cbar+1))
      (polyAdd (cap (C+1)) (cap (Cbar + -C))) :=
    (RatPolyCoeffEqv.smul_coefficient (poly_identity_of_normal_eq
      (.add (.var 0) (.const 1))
      (.add (.add (.var 1) (.const 1)) (.add (.var 0) (.neg (.var 1))))
      (by decide) (fun | 0 => Cbar | _ => C)) polyOne).trans
      (cap_add (C+1) (Cbar + -C)).symm
  exact Certificate.ofCoeff
    (((hcap.mul (RatPolyCoeffEqv.refl _)).add (RatPolyCoeffEqv.refl _)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.add (.var 0) (.var 1)) (.var 2)) (.var 3))
        (.add (.add (.mul (.var 0) (.var 2)) (.var 3)) (.mul (.var 1) (.var 2)))
        (by decide) (fun
          | 0 => cap (C+1)
          | 1 => cap (Cbar + -C)
          | 2 => polyMul (threeSquare u) (polyMul p p)
          | _ => polyAdd (polyMul p (quadraticForm u ddp))
              (polyNeg (polyMul (firstJet u dp) (firstJet u dp))))))
    (V.add S)

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixCurvature

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixCurvature.precisionFloor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixCurvature.plaquetteCurvatureTolerance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixCurvature.plaquetteCurvatureCutoff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixCurvature.plaquetteCurvatureCost
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixCurvature.plaquettePrefixFrozenCurvature
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixCurvature.precisionFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixCurvature.plaquetteCurvatureTolerance_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixCurvature.plaquettePrefix_frozen_curvature_nearFlat_certificate
