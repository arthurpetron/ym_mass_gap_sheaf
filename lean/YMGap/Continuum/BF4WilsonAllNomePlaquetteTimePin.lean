/-
# All-nome plaquette time correlations on the existing joint carrier

The old fixed-width reflected pairing and the literal Wilson lag moment
have the SAME finite window ratio after the proved source-polynomial pin.
Their actual joint diagonal limits agree; right padding removes the unused
half-window. This is a scalar identity, not a whole-carrier identification.

Centering cancels from the correlation loss. Thus the all-nome Wilson time
increment is twice the loss of the EXISTING centered plaquette correlation.
No positive-time survival, spatial limit or physical time calibration follows.
-/
import YMGap.Continuum.BF4WilsonPlaquetteSourcePin
import YMGap.Continuum.BF4WilsonAllNomeTimeIncrement
import YMGap.Continuum.BF4ExactSlabFixedSpatialLocalVariance

namespace YMGap.Continuum.BF4WilsonAllNomePlaquetteTimePin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceCharacter (faceSpan faceSpan_radius)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (physicalTime physicalTime_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator (chartScalar chartScalar_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm (jointCenteredMoment)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette (plaquetteLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonLimitStationarity (originalJoint_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws (windowRatio_congr)
open YMGap.Continuum.BF4WilsonAllNomeMomentConvexity
open YMGap.Continuum.BF4WilsonAllNomeTimeIncrement
open YMGap.Continuum.BF4WilsonJointFunctionalLaws (equiv_sub)
open YMGap.Continuum.BF4WilsonPlaquetteSourcePin

attribute [local irreducible] chartScalar chartJointLimit jointPairing originalJointLimit originalWindowScalar

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)

local notation "x" => faceSpan width face hf
local notation "loop" => plaquetteLoop face hf

/-- Both existing scalar limits are reached from the SAME original finite
window ratio. Their representative Cauchy moduli are not equated. -/
theorem jointPairing_lag (n : Nat) :
    Equiv (jointPairing hw0 hw1 width x (physicalTime n x))
      (lagMoment hw0 hw1 loop n) := by
  have hx : BF4ExactSlabFixedSpatialIntrinsicReflectedForm.radius (x).val ≤ n := by
    rw [faceSpan_radius]
    exact Nat.zero_le _
  have hy := face_time_radius width face hf n
  have he : Within (2*n) (lagExpression loop n) :=
    ⟨by change n ≤ 2*n; omega, Nat.zero_le _⟩
  have hlimits : Equiv (chartJointLimit hw0 hw1 width n x (physicalTime n x) hx hy)
      (originalJointLimit hw0 hw1 (2*n) (lagExpression loop n) he) := by
    apply Equiv_of_limit_of_equal ?_
      (chartJoint_diagonal_converges hw0 hw1 width n x (physicalTime n x) hx hy)
      (originalJoint_diagonal_converges hw0 hw1 (2*n) (lagExpression loop n) he)
    intro stage
    apply SumOfSquares.Equiv_of_approx_eqv
    intro k
    exact Q'.eqv_trans _ _ _ (chartScalar_pin hw0 hw1 width stage n x (physicalTime n x) hx hy stage)
      (Q'.eqv_trans _ _ _
        (windowRatio_congr hw0 hw1 _ width (Nat.le_add_right _ _) stage (2*n) stage
          (mixedProduct_lag width face hf n))
        (Q'.eqv_symm (originalWindowScalar_pin hw0 hw1 (2*n) (lagExpression loop n) he stage stage stage)))
  have hp : Equiv (originalJointLimit hw0 hw1 (2*n) (lagExpression loop n) he)
      (lagMoment hw0 hw1 loop n) := by
    simpa only [Nat.add_zero, ←Nat.two_mul, shift_zero, lagMoment] using
      originalJoint_padding hw0 hw1 n 0 n (lagExpression loop n) (lag_within loop n)
  exact (jointPairing_chart hw0 hw1 width n x (physicalTime n x) hx hy).trans (hlimits.trans hp)

private theorem common_sub_cancel (a b m : CReal) :
    Equiv (sub (sub a m) (sub b m)) (sub a b) :=
  SumOfSquares.Equiv_of_approx_eqv (fun k =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 2))) (.neg (.add (.var 1) (.neg (.var 2)))))
      (.add (.var 0) (.neg (.var 1))) (by decide)
      (fun | 0 => a.approx k | 1 => b.approx k | _ => m.approx k))

/-- The actual centering coefficients are independent of the lag and cancel
exactly. No separately chosen stationary mean is inserted. -/
theorem centered_loss_pin (n : Nat) :
    Equiv (sub (jointCenteredMoment hw0 hw1 width 0 x x)
      (jointCenteredMoment hw0 hw1 width n x x))
      (sub (lagMoment hw0 hw1 loop 0) (lagMoment hw0 hw1 loop n)) := by
  exact (common_sub_cancel _ _ _).trans
    (equiv_sub (jointPairing_lag hw0 hw1 width face hf 0)
      (jointPairing_lag hw0 hw1 width face hf n))

/-- The Wilson squared increment is twice the loss of the SAME existing
centered reflected time correlation, at every natural lag and every nome. -/
theorem timeIncrement_centered_pin (n : Nat) :
    Equiv (timeIncrement hw0 hw1 loop n)
      (mul (ofQ' 2) (sub (jointCenteredMoment hw0 hw1 width 0 x x)
        (jointCenteredMoment hw0 hw1 width n x x))) :=
  (timeIncrement_pin hw0 hw1 loop n).trans
    (Pivot2.mul_congr_right (centered_loss_pin hw0 hw1 width face hf n).symm)

end YMGap.Continuum.BF4WilsonAllNomePlaquetteTimePin

#print axioms YMGap.Continuum.BF4WilsonAllNomePlaquetteTimePin.jointPairing_lag
#print axioms YMGap.Continuum.BF4WilsonAllNomePlaquetteTimePin.centered_loss_pin
#print axioms YMGap.Continuum.BF4WilsonAllNomePlaquetteTimePin.timeIncrement_centered_pin
