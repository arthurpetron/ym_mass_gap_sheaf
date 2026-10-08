/-
# Full frozen-direction curvature of the SAME ORIGINAL heat prefix

All nine actual mixed jets meet the N=K+1 weighted finite heat, with literal
signed errors. Arbitrary supported polynomial direction coefficients are
frozen, not differentiated or magnitude-bounded. The existing six-column
envelope's factor is paid by the named tolerance/onset, not the cost.

Scope: original blocks zero/one, fixed strict nome. This is not arbitrary
block recoding, interacting conditional score, OS, spacing control or a
physical Hamiltonian gap. Those joins remain separate obligations.
-/

import YMGap.Continuum.SU2QuaternionPairedHeatPrefixMixedDeficit
import YMGap.Continuum.SU2QuaternionPairedFrozenJacobiCurvature
import YMGap.Continuum.QuaternionHaarFrozenCurvatureApproximation
import YMGap.Continuum.SU2QuaternionPairedHeatPrefixCurvature

namespace YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixCurvature

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_add cap_mul_left)
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame (threeSquare)
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (pairedDerivative)
open YMGap.Continuum.SU2QuaternionPairedScalarSquare (relativeWord_supported relativeWord_unit)
open YMGap.Continuum.SU2QuaternionPairedHeatPrefixDeficit
open YMGap.Continuum.SU2QuaternionPairedHeatPrefixMixedDeficit
open YMGap.Continuum.SU2QuaternionPairedFrozenJacobiCurvature
  (frozen_curvature_certificate frozen_curvature_nearFlat_certificate)
open YMGap.Continuum.SU2QuaternionPairedHeatPrefixCurvature (prefixCurvatureCost)
open YMGap.Continuum.JacobiHeatRadialProducedBound
  (radialCap radialOnset radialOnset_small_factor radialCap_nonnegative
    nearFlatRadialCap nearFlatRadialCap_nonnegative)
open YMGap.Continuum.JacobiHeatPrefixCurvaturePrecision
  (curvatureCap curvatureCap_nonnegative radialCap_le_curvatureCap
    nearFlatCurvatureCap nearFlatCurvatureCap_nonnegative nearFlatRadialOnset
    nearFlatRadialOnset_small_factor nearFlatRadialCap_le_curvatureCap)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headFloor_positive headCutoff)

/-- Quarter-floor precision pays factor six without changing the final cost. -/
def precisionFloor (w : Q') : Q' := HalfPow.half*(HalfPow.half*headFloor w)

def prefixFrozenCurvatureTolerance (w : Q') : Q' :=
  JacobiHeatPrefixCurvaturePrecision.errorTolerance (precisionFloor w) (curvatureCap w)
    (prefixValueCap w) (prefixFirstCap w) (prefixSecondCap w)

/-- Fixed before the actual finite cutoff is selected; no direction dependence. -/
def prefixFrozenCurvatureCutoff (w : Q') : Nat :=
  max (headCutoff w) (max (radialOnset w)
    (pairedDeficitCutoff w (prefixFrozenCurvatureTolerance w)))

def prefixFrozenCurvature (w C : Q') (K : Nat) (u : Fin 3 → RatPoly) : RatPoly :=
  let p := pairedPrefix w K
  QuaternionHaarFrozenCurvatureApproximation.jetCurvature C p
    (fun i => pairedDerivative i p) (fun i j => pairedDerivative i (pairedDerivative j p)) u

theorem precisionFloor_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (0 : Q') < precisionFloor w :=
  HKPos.q_mul_pos (by decide : (0 : Q') < HalfPow.half)
    (HKPos.q_mul_pos (by decide : (0 : Q') < HalfPow.half) (headFloor_positive hw0 hw1))

theorem prefixFrozenCurvatureTolerance_positive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (0 : Q') < prefixFrozenCurvatureTolerance w :=
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

/-- Produced full matrix on the literal ORIGINAL prefix, at the adaptive cost. -/
def prefix_frozen_curvature_adaptive_certificate {blocks : Nat} {w : Q'}
    (hb : 1 < blocks) (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : prefixFrozenCurvatureCutoff w ≤ K) (u : Fin 3 → RatPoly)
    (hu : ∀ i, SupportedQuaternionBlocks blocks (u i)) :
    Certificate blocks (prefixFrozenCurvature w ((radialCap w (K+1)+1)+1) K u) := by
  have hhead : headCutoff w ≤ K := by unfold prefixFrozenCurvatureCutoff at hK; omega
  have hradial : radialOnset w ≤ K+1 := by unfold prefixFrozenCurvatureCutoff at hK; omega
  have herror : pairedDeficitCutoff w (prefixFrozenCurvatureTolerance w) ≤ K := by
    unfold prefixFrozenCurvatureCutoff at hK
    omega
  let P := prefix_value_interval hb hw0 hw1 K
  let DP := prefix_first_interval hb hw0 hw1 K
  let DDP := prefix_mixed_interval hb hw0 hw1 K
  let E := deficit_value_interval hb hw0 hw1 (prefixFrozenCurvatureTolerance_positive hw0 hw1) K herror
  let DE := deficit_first_interval hb hw0 hw1 (prefixFrozenCurvatureTolerance_positive hw0 hw1) K herror
  let DDE := deficit_mixed_interval hb hw0 hw1 (prefixFrozenCurvatureTolerance_positive hw0 hw1) K herror
  let C := radialCap w (K+1)+1
  have hC : (0 : Q') ≤ C := Q'.zero_le_add _ _ (radialCap_nonnegative hw0 _) Q'.zero_le_one
  have hbudget : 6*QuaternionHaarCurvatureApproximation.errorCap C
      (prefixValueCap w) (prefixFirstCap w) (prefixSecondCap w)
      (prefixFrozenCurvatureTolerance w) (2*prefixFrozenCurvatureTolerance w)
      (4*prefixFrozenCurvatureTolerance w) ≤ headFloor w*headFloor w :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ 6
        (JacobiHeatPrefixCurvaturePrecision.error_budget (precisionFloor_positive hw0 hw1) hC
          (curvatureCap_nonnegative hw0) (radialCap_le_curvatureCap hw0 hw1 (K+1))
          P.nonnegative (DP 0).nonnegative (DDP 0 0).nonnegative) (by decide))
      (six_quarter_square_le (headFloor w))
  let floor := QuaternionHaarAllNomeHeatCertificate.prefixFloorCertificate hw0 hw1
    (relativeWord_supported hb) (relativeWord_unit hb) K hhead
  let weighted := frozen_curvature_certificate hb hw0 hw1 (K+1) (by omega)
    (radialOnset_small_factor hw0 hw1 (K+1) hradial) (by decide : (0 : Q') < 1) u hu
  exact QuaternionHaarFrozenCurvatureApproximation.curvature_approximation_certificate u hu
    hC (Q'.le_of_lt (headFloor_positive hw0 hw1)) (prefix_split_pin hw0 hw1 K)
    (prefix_first_split_pin hw0 hw1 K) (prefix_mixed_split_pin hw0 hw1 K)
    P E DP DE DDP DDE hbudget floor weighted

/-- Full SAME original matrix with a cutoff/carrier/direction-independent cost,
at the named strict nome. No near-one/scaling uniformity is asserted. -/
def prefix_frozen_curvature_certificate {blocks : Nat} {w : Q'}
    (hb : 1 < blocks) (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : prefixFrozenCurvatureCutoff w ≤ K) (u : Fin 3 → RatPoly)
    (hu : ∀ i, SupportedQuaternionBlocks blocks (u i)) :
    Certificate blocks (prefixFrozenCurvature w (prefixCurvatureCost w) K u) := by
  let p := pairedPrefix w K
  let C := radialCap w (K+1)+1
  let Cbar := curvatureCap w
  let P := prefix_value_interval hb hw0 hw1 K
  let V := prefix_frozen_curvature_adaptive_certificate hb hw0 hw1 K hK u hu
  let direction : Certificate blocks (threeSquare u) :=
    (Certificate.square (u 0) (hu 0)).add
      ((Certificate.square (u 1) (hu 1)).add (Certificate.square (u 2) (hu 2)))
  let S := Certificate.ofCoeff (cap_mul_left (Cbar + -C) (polyMul (threeSquare u) (polyMul p p)))
    (Certificate.smul (Cbar + -C)
      (Q'.sub_nonneg_of_le (radialCap_le_curvatureCap hw0 hw1 (K+1)))
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
          | 0 => cap (C+1) | 1 => cap (Cbar + -C)
          | 2 => polyMul (threeSquare u) (polyMul p p)
          | _ => polyAdd
              (polyMul p (QuaternionHaarThreePolynomialMatrixEnvelope.quadraticForm u
                (fun i j => pairedDerivative i (pairedDerivative j p))))
              (polyNeg (polyMul
                (QuaternionHaarFrozenCurvatureApproximation.firstJet u (fun i => pairedDerivative i p))
                (QuaternionHaarFrozenCurvatureApproximation.firstJet u (fun i => pairedDerivative i p)))))))
    (V.add S)

/-- Sharper produced envelope; all original-prefix discrepancy caps are retained. -/
def nearFlatPrefixFrozenCurvatureTolerance (w : Q') : Q' :=
  JacobiHeatPrefixCurvaturePrecision.errorTolerance (precisionFloor w) (nearFlatCurvatureCap w)
    (prefixValueCap w) (prefixFirstCap w) (prefixSecondCap w)

/-- Head floor, actual finite tail and six-column approximation are all paid. -/
def nearFlatPrefixFrozenCurvatureCutoff (w : Q') : Nat :=
  max (headCutoff w) (max (nearFlatRadialOnset w)
    (pairedDeficitCutoff w (nearFlatPrefixFrozenCurvatureTolerance w)))

def nearFlatPrefixCurvatureCost (w : Q') : Q' := nearFlatCurvatureCap w+1

/-- Sharper full frozen matrix on the SAME ORIGINAL character prefix, for every
strict nome and supported frozen direction. No interacting marginal or signed
source-weighted innovation payment is supplied by this Haar certificate. -/
def prefix_frozen_curvature_nearFlat_certificate {blocks : Nat} {w : Q'}
    (hb : 1 < blocks) (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : nearFlatPrefixFrozenCurvatureCutoff w ≤ K) (u : Fin 3 → RatPoly)
    (hu : ∀ i, SupportedQuaternionBlocks blocks (u i)) :
    Certificate blocks (prefixFrozenCurvature w (nearFlatPrefixCurvatureCost w) K u) := by
  have hhead : headCutoff w ≤ K := by unfold nearFlatPrefixFrozenCurvatureCutoff at hK; omega
  have hradial : nearFlatRadialOnset w ≤ K+1 := by
    unfold nearFlatPrefixFrozenCurvatureCutoff at hK
    omega
  have herror : pairedDeficitCutoff w (nearFlatPrefixFrozenCurvatureTolerance w) ≤ K := by
    unfold nearFlatPrefixFrozenCurvatureCutoff at hK
    omega
  have ht : (0 : Q') < nearFlatPrefixFrozenCurvatureTolerance w :=
    JacobiHeatPrefixCurvaturePrecision.errorTolerance_positive (precisionFloor_positive hw0 hw1)
  let p := pairedPrefix w K
  let C := nearFlatRadialCap w (K+1)+1
  let Cbar := nearFlatCurvatureCap w
  have hC : (0 : Q') ≤ C :=
    Q'.zero_le_add _ _ (nearFlatRadialCap_nonnegative hw0 _) Q'.zero_le_one
  have hCCbar : C ≤ Cbar := nearFlatRadialCap_le_curvatureCap hw0 hw1 (K+1) hradial
  let P := prefix_value_interval hb hw0 hw1 K
  let DP := prefix_first_interval hb hw0 hw1 K
  let DDP := prefix_mixed_interval hb hw0 hw1 K
  let E := deficit_value_interval hb hw0 hw1 ht K herror
  let DE := deficit_first_interval hb hw0 hw1 ht K herror
  let DDE := deficit_mixed_interval hb hw0 hw1 ht K herror
  have hbudget : 6*QuaternionHaarCurvatureApproximation.errorCap C
      (prefixValueCap w) (prefixFirstCap w) (prefixSecondCap w)
      (nearFlatPrefixFrozenCurvatureTolerance w) (2*nearFlatPrefixFrozenCurvatureTolerance w)
      (4*nearFlatPrefixFrozenCurvatureTolerance w) ≤ headFloor w*headFloor w :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ 6
        (JacobiHeatPrefixCurvaturePrecision.error_budget (precisionFloor_positive hw0 hw1) hC
          (nearFlatCurvatureCap_nonnegative hw0) hCCbar
          P.nonnegative (DP 0).nonnegative (DDP 0 0).nonnegative) (by decide))
      (six_quarter_square_le (headFloor w))
  let floor := QuaternionHaarAllNomeHeatCertificate.prefixFloorCertificate hw0 hw1
    (relativeWord_supported hb) (relativeWord_unit hb) K hhead
  let weighted := frozen_curvature_nearFlat_certificate hb hw0 hw1 (K+1) (by omega)
    (nearFlatRadialOnset_small_factor hw0 hw1 (K+1) hradial) (by decide : (0 : Q') < 1) u hu
  let V := QuaternionHaarFrozenCurvatureApproximation.curvature_approximation_certificate u hu
    hC (Q'.le_of_lt (headFloor_positive hw0 hw1)) (prefix_split_pin hw0 hw1 K)
    (prefix_first_split_pin hw0 hw1 K) (prefix_mixed_split_pin hw0 hw1 K)
    P E DP DE DDP DDE hbudget floor weighted
  let direction : Certificate blocks (threeSquare u) :=
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
          | 0 => cap (C+1) | 1 => cap (Cbar + -C)
          | 2 => polyMul (threeSquare u) (polyMul p p)
          | _ => polyAdd
              (polyMul p (QuaternionHaarThreePolynomialMatrixEnvelope.quadraticForm u
                (fun i j => pairedDerivative i (pairedDerivative j p))))
              (polyNeg (polyMul
                (QuaternionHaarFrozenCurvatureApproximation.firstJet u (fun i => pairedDerivative i p))
                (QuaternionHaarFrozenCurvatureApproximation.firstJet u (fun i => pairedDerivative i p)))))))
    (V.add S)

end YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixCurvature

#print axioms YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixCurvature.precisionFloor
#print axioms YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixCurvature.prefixFrozenCurvatureTolerance
#print axioms YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixCurvature.prefixFrozenCurvatureCutoff
#print axioms YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixCurvature.precisionFloor_positive
#print axioms YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixCurvature.prefixFrozenCurvatureTolerance_positive
#print axioms YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixCurvature.prefix_frozen_curvature_adaptive_certificate
#print axioms YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixCurvature.prefix_frozen_curvature_certificate
#print axioms YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixCurvature.nearFlatPrefixFrozenCurvatureTolerance
#print axioms YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixCurvature.nearFlatPrefixFrozenCurvatureCutoff
#print axioms YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixCurvature.nearFlatPrefixCurvatureCost
#print axioms YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixCurvature.prefix_frozen_curvature_nearFlat_certificate
