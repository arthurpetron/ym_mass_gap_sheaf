/-
# Inactive-face cancellation on the original all-nome Wilson carrier

The existing full-action finite fringe-face identity passes through the
actual joint heat-cutoff/time limit. Both endpoint means are identified by
the original stationarity theorem, not by a separate invariant measure.
The resulting centered Wilson moment is zero at every positive integer lag.
Only faces with an inactive kinetic link are covered; the interacting bulk
and continuum theory are not refuted by this boundary cancellation.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceCorrelations
import YMGap.Continuum.BF4WilsonAllNomePlaquetteVariance
import YMGap.Continuum.SeriesComposition

namespace YMGap.Continuum.BF4WilsonAllNomeFringeCorrelation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceGeometry (FullyActive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceCorrelations (window_connected_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHaar (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws (windowRatio_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonLimitStationarity (originalJoint_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift shift_zero)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4WilsonAllNomeMomentConvexity
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm (intrinsicForm intrinsicForm_symm)
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState pairing_lag)
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments (centeredTimeMoment)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteVariance (literal_mean_pin)
open YMGap.Continuum.BF4WilsonJointFunctionalLaws (equiv_sub)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_coeff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] originalWindowScalar originalJointLimit baseLinks

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)

local notation "loop" => plaquetteLoop face hf
local notation "e0" => (WindowExpression.loop 0 loop 1)
local notation "M" => originalJointLimit hw0 hw1 0 e0 (Nat.le_refl 0)

/-- The same original partition occurs in all three terms. The regulator
stage is positive only to retain the fundamental character in the cutoff. -/
theorem finite_connected_zero (ha : ¬ FullyActive width face) (r j : Nat)
    (hj : 1 ≤ j) :
    originalWindowScalar hw0 hw1 (r+1) (lagExpression loop (r+1)) j j j +
      -(originalWindowScalar hw0 hw1 (r+1) e0 j j j *
        originalWindowScalar hw0 hw1 (r+1) (.loop (r+1) loop 1) j j j) ≈ 0 := by
  let f := characterPolynomial (plaquette width face).scalar 1
  have h0 : RatPolyCoeffEqv (sourcePolynomial e0) f := by
    simpa only [sourcePolynomial, Nat.zero_mul, liftBoundary] using
      sourceCharacter_plaquette width face 1
  have h1 : RatPolyCoeffEqv (sourcePolynomial (.loop (r+1) loop 1))
      (liftBoundary ((r+1)*(N width)) f) := by
    simpa only [sourcePolynomial] using
      lift_coeff ((r+1)*(N width)) (sourceCharacter_plaquette width face 1)
  have hp : RatPolyCoeffEqv (sourcePolynomial (lagExpression loop (r+1)))
      (polyMul f (liftBoundary ((r+1)*(N width)) f)) :=
    (h1.mul h0).trans (RatPolyCoeffEqv.mul_comm _ _)
  have p0 := Q'.eqv_trans _ _ _
    (originalWindowScalar_pin hw0 hw1 (r+1) e0 (Nat.zero_le _) j j j)
    (windowRatio_congr hw0 hw1 _ width (Nat.le_add_right _ _) j (r+1) j h0)
  have p1 := Q'.eqv_trans _ _ _
    (originalWindowScalar_pin hw0 hw1 (r+1) (.loop (r+1) loop 1) (Nat.le_refl _) j j j)
    (windowRatio_congr hw0 hw1 _ width (Nat.le_add_right _ _) j (r+1) j h1)
  have pp := Q'.eqv_trans _ _ _
    (originalWindowScalar_pin hw0 hw1 (r+1) (lagExpression loop (r+1))
      (lag_within loop (r+1)) j j j)
    (windowRatio_congr hw0 hw1 _ width (Nat.le_add_right _ _) j (r+1) j hp)
  have he := Q'.add_eqv_congr' pp (Q'.neg_eqv_congr _ _
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ p0)
      (Q'.mul_eqv_congr_left _ _ _ p1)))
  exact Q'.eqv_trans _ _ _ he
    (window_connected_zero hw0 hw1 (headCutoff w+j) width (Nat.le_add_right _ _)
      (by omega) j r j hf ha f (plaquette_supported width face))

private theorem lower_mean_converges (n : Nat) :
    ConvergesTo (fun j => ofQ' (originalWindowScalar hw0 hw1 n e0 j j j)) M := by
  have hp : Equiv (originalJointLimit hw0 hw1 n e0 (Nat.zero_le _)) M := by
    simpa only [Nat.zero_add, shift_zero] using
      originalJoint_padding hw0 hw1 0 0 n e0 (Nat.le_refl 0)
  exact ArctanTrigConvergesProof.convergesTo_of_equiv
    (originalJoint_diagonal_converges hw0 hw1 n e0 (Nat.zero_le _)) hp

private theorem upper_mean_converges (n : Nat) :
    ConvergesTo (fun j => ofQ'
      (originalWindowScalar hw0 hw1 n (.loop n loop 1) j j j)) M := by
  have hp : Equiv (originalJointLimit hw0 hw1 n (.loop n loop 1) (Nat.le_refl _)) M := by
    simpa only [Nat.zero_add, Nat.add_zero, shift, mapOffsets] using
      originalJoint_padding hw0 hw1 0 n 0 e0 (Nat.le_refl 0)
  exact ArctanTrigConvergesProof.convergesTo_of_equiv
    (originalJoint_diagonal_converges hw0 hw1 n (.loop n loop 1) (Nat.le_refl _)) hp

private theorem connected_diagonal_converges (n : Nat) :
    ConvergesTo (fun j => ofQ'
      (originalWindowScalar hw0 hw1 n (lagExpression loop n) j j j +
        -(originalWindowScalar hw0 hw1 n e0 j j j *
          originalWindowScalar hw0 hw1 n (.loop n loop 1) j j j)))
      (sub (lagMoment hw0 hw1 loop n) (mul M M)) := by
  have h := TrigAddCReal.convergesTo_add
    (originalJoint_diagonal_converges hw0 hw1 n (lagExpression loop n) (lag_within loop n))
    (TrigAddCReal.convergesTo_neg
      (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
        (lower_mean_converges hw0 hw1 width face hf n)
        (upper_mean_converges hw0 hw1 width face hf n)))
  apply TrigAddCReal.convergesTo_congr_seq _ h
  intro j
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

/-- Both heat cutoff and exterior time are removed using their existing
joint-limit moduli. The source and positive lag stay fixed throughout. -/
theorem connected_lag_zero (ha : ¬ FullyActive width face) (r : Nat) :
    Equiv (sub (lagMoment hw0 hw1 loop (r+1)) (mul M M)) czero := by
  apply Equiv_of_limit_of_equal ?_
    (SeriesComposition.convergesTo_shift
      (connected_diagonal_converges hw0 hw1 width face hf (r+1)))
    (convergesTo_const czero)
  intro j
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ =>
    finite_connected_zero hw0 hw1 width face hf ha r (j+1) (by omega))

/-- The vanishing scalar is precisely the centered moment of the SAME
all-nome Wilson form, not a different Haar carrier's kernel. -/
theorem centeredTimeMoment_zero (ha : ¬ FullyActive width face) (r : Nat) :
    Equiv (centeredTimeMoment hw0 hw1 (r+1) (loopState loop) (loopState loop)) czero := by
  let u := BF4ExactSlabFixedSpatialWilsonIntrinsicForm.unit width
  have hm : Equiv (intrinsicForm hw0 hw1 (loopState loop) u) M :=
    literal_mean_pin hw0 hw1 width face hf
  have hm' : Equiv (intrinsicForm hw0 hw1 u (loopState loop)) M :=
    (intrinsicForm_symm hw0 hw1 u (loopState loop)).trans hm
  have hcenter : Equiv
      (centeredTimeMoment hw0 hw1 (r+1) (loopState loop) (loopState loop))
      (sub (lagMoment hw0 hw1 loop (r+1)) (mul M M)) := by
    unfold centeredTimeMoment
    exact equiv_sub (pairing_lag hw0 hw1 loop (r+1))
      ((Pivot2.mul_congr_left hm).trans (Pivot2.mul_congr_right hm'))
  exact hcenter.trans (connected_lag_zero hw0 hw1 width face hf ha r)

#print axioms finite_connected_zero
#print axioms connected_lag_zero
#print axioms centeredTimeMoment_zero

end YMGap.Continuum.BF4WilsonAllNomeFringeCorrelation
