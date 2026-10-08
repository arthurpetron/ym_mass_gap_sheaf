/-
# Produced paired curvature of the ORIGINAL unweighted heat prefix

The actual K+1 Jacobi heat certificate meets the original value and two
paired-jet deficit producers. A cutoff-independent envelope is fixed before
choosing the error tolerance, so the explicit cutoff has no circular input.
The original heat floor pays only approximation precision. The final cost
contains no inverse floor and is independent of cutoff and carrier size.

Scope: at each strict nome, separately in the three paired directions on
original blocks zero and one. This is not a full frozen-direction matrix,
arbitrary-block recoding, interacting conditional estimate, OS transfer
bound, spacing-uniform estimate or physical mass calibration.
-/

import YMGap.Continuum.SU2QuaternionPairedHeatPrefixDeficit
import YMGap.Continuum.QuaternionHaarCurvatureApproximation
import YMGap.Continuum.JacobiHeatPrefixCurvaturePrecision

namespace YMGap.Continuum.SU2QuaternionPairedHeatPrefixCurvature

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (pairedDerivative)
open YMGap.Continuum.SU2QuaternionPairedScalarSquare (relativeWord_supported relativeWord_unit)
open YMGap.Continuum.SU2QuaternionPairedJacobiCurvature (pairedHeat pairedCurvature paired_curvature_certificate)
open YMGap.Continuum.SU2QuaternionPairedHeatPrefixDeficit
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_add cap_mul_left)
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarCurvatureApproximation (jetCurvature curvature_approximation_certificate)
open YMGap.Continuum.JacobiHeatRadialProducedBound (radialCap radialOnset radialOnset_small_factor radialCap_nonnegative)
open YMGap.Continuum.JacobiHeatPrefixCurvaturePrecision
  (curvatureCap curvatureCap_nonnegative radialCap_le_curvatureCap)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headFloor_positive headCutoff)

/-- Fixed-nome cost; no cutoff, carrier size or inverse heat minimum. -/
def prefixCurvatureCost (w : Q') : Q' := curvatureCap w+1

/-- Original floor enters only the required approximation precision. -/
def prefixCurvatureTolerance (w : Q') : Q' :=
  JacobiHeatPrefixCurvaturePrecision.errorTolerance (headFloor w) (curvatureCap w)
    (prefixValueCap w) (prefixFirstCap w) (prefixSecondCap w)

/-- One explicit, carrier-independent cutoff joins all actual producers. -/
def prefixCurvatureCutoff (w : Q') : Nat :=
  max (headCutoff w) (max (radialOnset w) (pairedDeficitCutoff w (prefixCurvatureTolerance w)))

/-- Curvature of the literal ORIGINAL value and actual paired derivatives. -/
def prefixCurvature (w C : Q') (K : Nat) (i : Fin 3) : RatPoly :=
  let p := pairedPrefix w K
  jetCurvature C p (pairedDerivative i p) (pairedDerivative i (pairedDerivative i p))

theorem prefixCurvatureTolerance_positive {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (0 : Q') < prefixCurvatureTolerance w :=
  JacobiHeatPrefixCurvaturePrecision.errorTolerance_positive (headFloor_positive hw0 hw1)

/-- Produced certificate at the retained finite radial cost plus two.
No curvature or coordinate-cone premise is supplied by the caller. -/
def prefix_curvature_adaptive_certificate {blocks : Nat} {w : Q'}
    (hb : 1 < blocks) (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : prefixCurvatureCutoff w ≤ K) (i : Fin 3) :
    Certificate blocks (prefixCurvature w ((radialCap w (K+1)+1)+1) K i) := by
  have hhead : headCutoff w ≤ K := by unfold prefixCurvatureCutoff at hK; omega
  have hradial : radialOnset w ≤ K+1 := by unfold prefixCurvatureCutoff at hK; omega
  have herror : pairedDeficitCutoff w (prefixCurvatureTolerance w) ≤ K := by
    unfold prefixCurvatureCutoff at hK
    omega
  let P := prefix_value_interval hb hw0 hw1 K
  let DP := prefix_first_interval hb hw0 hw1 K i
  let DDP := prefix_second_interval hb hw0 hw1 K i
  let E := deficit_value_interval hb hw0 hw1 (prefixCurvatureTolerance_positive hw0 hw1) K herror
  let DE := deficit_first_interval hb hw0 hw1 (prefixCurvatureTolerance_positive hw0 hw1) K herror i
  let DDE := deficit_second_interval hb hw0 hw1 (prefixCurvatureTolerance_positive hw0 hw1) K herror i
  let C := radialCap w (K+1)+1
  have hC : (0 : Q') ≤ C := Q'.zero_le_add _ _ (radialCap_nonnegative hw0 _) Q'.zero_le_one
  have hbudget : QuaternionHaarCurvatureApproximation.errorCap C
      (prefixValueCap w) (prefixFirstCap w) (prefixSecondCap w)
      (prefixCurvatureTolerance w) (2*prefixCurvatureTolerance w) (4*prefixCurvatureTolerance w) ≤
      headFloor w*headFloor w :=
    JacobiHeatPrefixCurvaturePrecision.error_budget (headFloor_positive hw0 hw1) hC
      (curvatureCap_nonnegative hw0) (radialCap_le_curvatureCap hw0 hw1 (K+1))
      P.nonnegative DP.nonnegative DDP.nonnegative
  let floor := QuaternionHaarAllNomeHeatCertificate.prefixFloorCertificate hw0 hw1
    (relativeWord_supported hb) (relativeWord_unit hb) K hhead
  let weighted := paired_curvature_certificate hb hw0 hw1 (K+1) (by omega)
    (radialOnset_small_factor hw0 hw1 (K+1) hradial) (by decide : (0 : Q') < 1) i
  exact curvature_approximation_certificate hC (Q'.le_of_lt (headFloor_positive hw0 hw1))
    (prefix_split_pin hw0 hw1 K) (prefix_first_split_pin hw0 hw1 K i)
    (prefix_second_split_pin hw0 hw1 K i) P DP DDP E DE DDE hbudget floor weighted

/-- SAME original polynomial, with a cost independent of cutoff/carrier.
The nome is an explicit parameter; no uniformity near nome one is asserted. -/
def prefix_curvature_certificate {blocks : Nat} {w : Q'}
    (hb : 1 < blocks) (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : prefixCurvatureCutoff w ≤ K) (i : Fin 3) :
    Certificate blocks (prefixCurvature w (prefixCurvatureCost w) K i) := by
  let p := pairedPrefix w K
  let C := radialCap w (K+1)+1
  let Cbar := curvatureCap w
  let P := prefix_value_interval hb hw0 hw1 K
  let V := prefix_curvature_adaptive_certificate hb hw0 hw1 K hK i
  let S := Certificate.ofCoeff (cap_mul_left (Cbar + -C) (polyMul p p))
    (Certificate.smul (Cbar + -C)
      (Q'.sub_nonneg_of_le (radialCap_le_curvatureCap hw0 hw1 (K+1)))
      (Certificate.square p P.support))
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
          | 2 => polyMul p p
          | _ => polyAdd (polyMul p (pairedDerivative i (pairedDerivative i p)))
              (polyNeg (polyMul (pairedDerivative i p) (pairedDerivative i p)))))) (V.add S)

end YMGap.Continuum.SU2QuaternionPairedHeatPrefixCurvature

#print axioms YMGap.Continuum.SU2QuaternionPairedHeatPrefixCurvature.prefixCurvatureCost
#print axioms YMGap.Continuum.SU2QuaternionPairedHeatPrefixCurvature.prefixCurvatureTolerance
#print axioms YMGap.Continuum.SU2QuaternionPairedHeatPrefixCurvature.prefixCurvatureCutoff
#print axioms YMGap.Continuum.SU2QuaternionPairedHeatPrefixCurvature.prefixCurvatureTolerance_positive
#print axioms YMGap.Continuum.SU2QuaternionPairedHeatPrefixCurvature.prefix_curvature_adaptive_certificate
#print axioms YMGap.Continuum.SU2QuaternionPairedHeatPrefixCurvature.prefix_curvature_certificate
