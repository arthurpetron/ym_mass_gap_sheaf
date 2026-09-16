/-
# Positive central-character variance after joint cutoff/boundary removal

The finite floor is tested at stage k+1 and boundary depth k+1, so both
moments follow the SAME shifted joint diagonal. The floor therefore passes
to the original joint reflected form. Its explicit positive rational
depends only on nome and positive spatial width, not the removed regulators.

The completed pairing's embedding pin transfers this to the Gram
determinant of the actual embedded character and the actual unit. This is
a nonconstant-observable witness, not a constructed centered completed
vector, non-Wick continuum field, spatial-uniform estimate or mass gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCentralVariance
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
import YMGap.Continuum.SeriesComposition
import YMGap.Continuum.ArctanTrigConvergesProof

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointCentralVariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialCentralCharacter (span)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCentralDensityFloor
open YMGap.Continuum.BF4ExactSlabFixedSpatialCentralVariance
open YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator (chartScalar)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (unit physicalTime_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner

private theorem rational_variance_converges {a b : Nat → Q'} {A B : CReal}
    (ha : ConvergesTo (fun k => ofQ' (a k)) A)
    (hb : ConvergesTo (fun k => ofQ' (b k)) B) :
    ConvergesTo (fun k => ofQ' (a k + -(b k*b k))) (sub A (mul B B)) := by
  have h : ConvergesTo
      (fun k => add (ofQ' (a k)) (neg (mul (ofQ' (b k)) (ofQ' (b k)))))
      (sub A (mul B B)) :=
    TrigAddCReal.convergesTo_add ha (TrigAddCReal.convergesTo_neg
      (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general hb hb))
  apply TrigAddCReal.convergesTo_congr_seq (s := fun k =>
    add (ofQ' (a k)) (neg (mul (ofQ' (b k)) (ofQ' (b k))))) _ h
  intro k
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (hwidth : 0 < width)

local notation "x" => span width hwidth
local notation "J" => jointPairing hw0 hw1 width
local notation "B" => completedInner hw0 hw1 width
local notation "e" => jointEmbedSpan hw0 hw1 width x
local notation "u" => jointCompletedUnit hw0 hw1 width

attribute [local irreducible] jointPairing chartJointLimit chartScalar

/-- Shift both regulator indices together; the zero-depth exception is
discarded by an explicit shift, not a hidden eventuality premise. -/
theorem central_diagonal_converges :
    ConvergesTo (fun k => ofQ' (chartScalar hw0 hw1 width (k+1) 0 x x (k+1))) (J x x) :=
  ArctanTrigConvergesProof.convergesTo_of_equiv
    (SeriesComposition.convergesTo_shift
      (chartJoint_diagonal_converges hw0 hw1 width 0 x x (Nat.le_refl 0) (Nat.le_refl 0)))
    (Equiv.symm (jointPairing_chart hw0 hw1 width 0 x x (Nat.le_refl 0) (Nat.le_refl 0)))

theorem central_mean_converges :
    ConvergesTo (fun k => ofQ' (chartScalar hw0 hw1 width (k+1) 0 x (unit width) (k+1)))
      (J x (unit width)) :=
  ArctanTrigConvergesProof.convergesTo_of_equiv
    (SeriesComposition.convergesTo_shift
      (chartJoint_diagonal_converges hw0 hw1 width 0 x (unit width) (Nat.le_refl 0) (Nat.le_refl 0)))
    (Equiv.symm (jointPairing_chart hw0 hw1 width 0 x (unit width) (Nat.le_refl 0) (Nat.le_refl 0)))

theorem central_variance_converges :
    ConvergesTo (fun k => ofQ'
      (chartScalar hw0 hw1 width (k+1) 0 x x (k+1) +
        -(chartScalar hw0 hw1 width (k+1) 0 x (unit width) (k+1) *
          chartScalar hw0 hw1 width (k+1) 0 x (unit width) (k+1))))
      (sub (J x x) (mul (J x (unit width)) (J x (unit width)))) :=
  rational_variance_converges (central_diagonal_converges hw0 hw1 width hwidth)
    (central_mean_converges hw0 hw1 width hwidth)

/-- The original central-face variance has the displayed strict positive
floor after BOTH regulator limits, at each fixed positive spatial width. -/
theorem central_joint_variance_floor :
    leEv (ofQ' (centralFraction hw0 hw1 width))
      (jointCenteredMoment hw0 hw1 width 0 x x) := by
  have hfloor := leEv_of_convergesTo_le
    (CReal.convergesTo_const (ofQ' (centralFraction hw0 hw1 width)))
    (central_variance_converges hw0 hw1 width hwidth)
    (fun k => leEv_ofQ'_of_approx_ge (fun _ => chart_variance_floor hw0 hw1 width hwidth (k+1) k))
  have he : Equiv (sub (J x x) (mul (J x (unit width)) (J x (unit width))))
      (jointCenteredMoment hw0 hw1 width 0 x x) := by
    unfold jointCenteredMoment
    rw [physicalTime_zero]
    exact Equiv_add (Equiv.refl _) (neg_congr
      (TrigSignedAdd.mul_congr_right (jointPairing_symm hw0 hw1 width x (unit width))))
  exact leEv_trans hfloor (leEv_of_equiv he)

/-- Original observable and original unit on the SAME newly completed
carrier. This scalar determinant needs no unconstructed real vector action. -/
theorem central_completed_gram_pin :
    RCsub (B e e) (RCmul (B e u) (B u e)) =
      Quotient.mk crealSetoid (jointCenteredMoment hw0 hw1 width 0 x x) := by
  unfold jointCompletedUnit
  rw [completedInner_embedSpan, completedInner_embedSpan, completedInner_embedSpan]
  unfold jointCenteredMoment
  rw [physicalTime_zero]
  rfl

theorem central_completed_gram_floor :
    RCle (Quotient.mk crealSetoid (ofQ' (centralFraction hw0 hw1 width)))
      (RCsub (B e e) (RCmul (B e u) (B u e))) := by
  rw [central_completed_gram_pin]
  exact central_joint_variance_floor hw0 hw1 width hwidth

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointCentralVariance

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCentralVariance.central_diagonal_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCentralVariance.central_mean_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCentralVariance.central_variance_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCentralVariance.central_joint_variance_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCentralVariance.central_completed_gram_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointCentralVariance.central_completed_gram_floor
