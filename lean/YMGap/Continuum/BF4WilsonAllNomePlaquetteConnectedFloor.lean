/-
# A positive connected plaquette response after both regulator limits

The original finite centered response is expanded BEFORE passing to the
joint cutoff/time limit. Each term then uses the existing fixed-source
Cauchy construction. Stationarity identifies both limiting endpoint means
with the original zero-window mean. The positive floor depends on nome and
spatial width; no spatial or spacing limit is taken.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowCenteredProduct
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteUniformResponse
import YMGap.Continuum.BF4WilsonAllNomeMomentConvexity
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette
import YMGap.Continuum.ArctanTrigConvergesProof

namespace YMGap.Continuum.BF4WilsonAllNomePlaquetteConnectedFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHaar (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteUniformResponse
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowCenteredProduct
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonLimitStationarity
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift shift_zero)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4WilsonAllNomeMomentConvexity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_coeff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] originalWindowScalar originalJointLimit baseLinks

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)

local notation "loop" => plaquetteLoop face hf
local notation "e0" => (WindowExpression.loop 0 loop 1)
local notation "e1" => (WindowExpression.loop 1 loop 1)
local notation "M" => originalJointLimit hw0 hw1 0 e0 (Nat.le_refl 0)

/-- The floor applies to three fixed original observables on the standard
diagonal, once the terminal depth and retained character cutoff are positive. -/
theorem finite_connected_floor
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width)
    (j : Nat) (hj : 1 ≤ j) :
    uniformFloor hw0 width ≤
      originalWindowScalar hw0 hw1 1 (lagExpression loop 1) j j j +
        -(originalWindowScalar hw0 hw1 1 e0 j j j *
          originalWindowScalar hw0 hw1 1 e1 j j j) := by
  let f := characterPolynomial (plaquette width face).scalar 1
  have h0 : RatPolyCoeffEqv (sourcePolynomial e0) f := by
    simpa only [sourcePolynomial, Nat.zero_mul, liftBoundary] using
      sourceCharacter_plaquette width face 1
  have h1 : RatPolyCoeffEqv (sourcePolynomial e1) (liftBoundary (N width) f) := by
    simpa only [sourcePolynomial, Nat.one_mul] using
      lift_coeff (N width) (sourceCharacter_plaquette width face 1)
  have hp : RatPolyCoeffEqv (sourcePolynomial (lagExpression loop 1))
      (polyMul f (liftBoundary (N width) f)) :=
    (h1.mul h0).trans (RatPolyCoeffEqv.mul_comm _ _)
  have p0 := Q'.eqv_trans _ _ _
    (originalWindowScalar_pin hw0 hw1 1 e0 (Nat.zero_le _) j j j)
    (windowRatio_congr hw0 hw1 _ width (Nat.le_add_right _ _) j 1 j h0)
  have p1 := Q'.eqv_trans _ _ _
    (originalWindowScalar_pin hw0 hw1 1 e1 (Nat.le_refl _) j j j)
    (windowRatio_congr hw0 hw1 _ width (Nat.le_add_right _ _) j 1 j h1)
  have pp := Q'.eqv_trans _ _ _
    (originalWindowScalar_pin hw0 hw1 1 (lagExpression loop 1) (lag_within loop 1) j j j)
    (windowRatio_congr hw0 hw1 _ width (Nat.le_add_right _ _) j 1 j hp)
  have he := Q'.add_eqv_congr' pp (Q'.neg_eqv_congr _ _ (qmul p0 p1))
  have h := centered_window_response_floor hw0 hw1 width face hf hactive
    (headCutoff w+j) (Nat.le_add_right _ _) (by omega) (j-1)
  simp only [Nat.sub_add_cancel hj] at h
  have hc := centered_product_pin hw0 hw1 (headCutoff w+j) width
    (Nat.le_add_right _ _) j (plaquette_supported width face)
  exact Q'.le_trans' _ _ _ h
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hc) (Q'.ge_of_eqv he))

private theorem lower_mean_converges :
    ConvergesTo (fun j => ofQ' (originalWindowScalar hw0 hw1 1 e0 j j j)) M := by
  have hp : Equiv (originalJointLimit hw0 hw1 1 e0 (Nat.zero_le _)) M := by
    simpa only [Nat.zero_add, shift_zero] using
      originalJoint_padding hw0 hw1 0 0 1 e0 (Nat.le_refl 0)
  exact ArctanTrigConvergesProof.convergesTo_of_equiv
    (originalJoint_diagonal_converges hw0 hw1 1 e0 (Nat.zero_le _)) hp

private theorem upper_mean_converges :
    ConvergesTo (fun j => ofQ' (originalWindowScalar hw0 hw1 1 e1 j j j)) M := by
  have hp : Equiv (originalJointLimit hw0 hw1 1 e1 (Nat.le_refl _)) M := by
    simpa only [Nat.zero_add, Nat.add_zero, shift, mapOffsets] using
      originalJoint_padding hw0 hw1 0 1 0 e0 (Nat.le_refl 0)
  exact ArctanTrigConvergesProof.convergesTo_of_equiv
    (originalJoint_diagonal_converges hw0 hw1 1 e1 (Nat.le_refl _)) hp

/-- Convergence is applied only after the varying finite center has been
eliminated. Both limiting means are pinned to the same original zero window. -/
theorem connected_diagonal_converges :
    ConvergesTo (fun j => ofQ'
      (originalWindowScalar hw0 hw1 1 (lagExpression loop 1) j j j +
        -(originalWindowScalar hw0 hw1 1 e0 j j j *
          originalWindowScalar hw0 hw1 1 e1 j j j)))
      (sub (lagMoment hw0 hw1 loop 1) (mul M M)) := by
  have h := TrigAddCReal.convergesTo_add
    (originalJoint_diagonal_converges hw0 hw1 1 (lagExpression loop 1) (lag_within loop 1))
    (TrigAddCReal.convergesTo_neg
      (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
        (lower_mean_converges hw0 hw1 width face hf)
        (upper_mean_converges hw0 hw1 width face hf)))
  apply TrigAddCReal.convergesTo_congr_seq _ h
  intro j
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

/-- A positive explicit floor after the cutoff and time limits, for the
SAME connected Wilson response at fixed nome and spatial width. -/
theorem connected_response_floor
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width) :
    leEv (ofQ' (uniformFloor hw0 width))
      (sub (lagMoment hw0 hw1 loop 1) (mul M M)) := by
  apply leEv_of_ofQ'_limit_le (convergesTo_const _)
    (connected_diagonal_converges hw0 hw1 width face hf)
  intro epsilon he
  exact ⟨1, fun j hj => Q'.le_trans' _ _ _
    (finite_connected_floor hw0 hw1 width face hf hactive j hj)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))⟩

end YMGap.Continuum.BF4WilsonAllNomePlaquetteConnectedFloor

#print axioms YMGap.Continuum.BF4WilsonAllNomePlaquetteConnectedFloor.finite_connected_floor
#print axioms YMGap.Continuum.BF4WilsonAllNomePlaquetteConnectedFloor.connected_diagonal_converges
#print axioms YMGap.Continuum.BF4WilsonAllNomePlaquetteConnectedFloor.connected_response_floor
