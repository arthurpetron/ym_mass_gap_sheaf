/-
# Sharp quantitative complex pairing continuity on the SAME reflected carrier

Sharp complex Cauchy--Schwarz removes the factor two from the earlier
pairing-continuity modulus.  The carrier, represented tests, test-norm ceiling,
and constructed limits are exactly those of the existing actual fixed-width
JointCompletion.

This is a finite fixed-spatial-volume continuity result.  It supplies no
spatial/scaling limit, continuous time, Hilbert completion, or Clay closure.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexCauchySchwarz
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPairingContinuity

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexSharpContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexification
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPresentedCompleteness
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexPairingContinuity
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexCauchySchwarz

private theorem rc_mul_mono_left {a b c : RC} (hc : RCnonneg c) (h : RCle a b) :
    RCle (RCmul c a) (RCmul c b) := by
  revert hc h
  refine Quotient.inductionOn₃ c a b ?_
  exact fun C A B hc h => leEv_mul_nonneg_left hc h

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "D" => jointSeminorm hw0 hw1 width
local notation "VC" => ComplexCarrier hw0 hw1 width
local notation "I" => inner hw0 hw1 width

/-- Sharp pairing-error bound in the actual complex norm. -/
theorem pairing_error_bound (x y test : VC) :
    RCle (valueNormSq (valueSub (I x test) (I y test)))
      (RCmul (complexDistSq hw0 hw1 width x y) (I test test).1) := by
  rw [← inner_sub_left]
  exact inner_cauchySchwarz hw0 hw1 width
    (complexSub hw0 hw1 width x y) test

/-- Sharp norm-to-pairing convergence estimate, with no factor-two loss. -/
theorem limit_pairing_error (X : PresentedComplexCauchy hw0 hw1 width) (test : VC)
    (epsilon : Q') (he : (0 : Q') < epsilon) (p : Nat)
    (hp : X.limitRate hw0 hw1 width epsilon ≤ p) :
    RCle (valueNormSq (valueSub (I (X.point hw0 hw1 width p) test)
      (I (X.limit hw0 hw1 width) test)))
      (RCmul (Quotient.mk crealSetoid (ofQ' epsilon)) (I test test).1) := by
  have h := rc_mul_mono_left (inner_nonnegative hw0 hw1 width test)
    (X.limit_converges hw0 hw1 width epsilon he p hp)
  rw [RCmul_comm (I test test).1
      (complexDistSq hw0 hw1 width (X.point hw0 hw1 width p)
        (X.limit hw0 hw1 width)),
    RCmul_comm (I test test).1 (Quotient.mk crealSetoid (ofQ' epsilon))] at h
  exact RCle_trans (pairing_error_bound hw0 hw1 width _ _ test) h

/-- Squared-norm tolerance for the sharp complex pairing estimate. -/
def pairingTolerance (Y : (D).Cauchy × (D).Cauchy) (epsilon : Q') : Q' :=
  Q'.divPos epsilon (testNormCap hw0 hw1 width Y)
    (testNormCap_positive hw0 hw1 width Y)

def pairingRate (X : PresentedComplexCauchy hw0 hw1 width)
    (Y : (D).Cauchy × (D).Cauchy) (epsilon : Q') : Nat :=
  X.limitRate hw0 hw1 width (pairingTolerance hw0 hw1 width Y epsilon)

/-- Genuine sharp epsilon-to-index modulus for squared complex pairing error. -/
theorem pairing_converges (X : PresentedComplexCauchy hw0 hw1 width)
    (Y : (D).Cauchy × (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (p : Nat) (hp : pairingRate hw0 hw1 width X Y epsilon ≤ p) :
    RCle (valueNormSq (valueSub
      (I (X.point hw0 hw1 width p) (representedTest hw0 hw1 width Y))
      (I (X.limit hw0 hw1 width) (representedTest hw0 hw1 width Y))))
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  let delta := pairingTolerance hw0 hw1 width Y epsilon
  have hd : (0 : Q') < delta :=
    Q'.divPos_pos _ _ _ he
  have hd0 : RCnonneg (Quotient.mk crealSetoid (ofQ' delta)) :=
    leEv_ofQ'_of_approx_ge (fun _ => Q'.le_of_lt hd)
  have hmono := rc_mul_mono_left hd0
    (representedTest_norm_le hw0 hw1 width Y)
  have hcancel : RCmul (Quotient.mk crealSetoid (ofQ' delta))
      (Quotient.mk crealSetoid (ofQ' (testNormCap hw0 hw1 width Y))) =
      Quotient.mk crealSetoid (ofQ' epsilon) :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      Q'.divPos_mul_eqv _ _ _))
  rw [hcancel] at hmono
  exact RCle_trans (limit_pairing_error hw0 hw1 width X
    (representedTest hw0 hw1 width Y) delta hd p hp) hmono

/-- Actual discrete-time complex matrix coefficients inherit the sharp modulus
on the same carrier.  Time remains discrete and fixed. -/
theorem time_pairing_converges (X : PresentedComplexCauchy hw0 hw1 width)
    (Y : (D).Cauchy × (D).Cauchy) (time : Nat)
    (epsilon : Q') (he : (0 : Q') < epsilon) (p : Nat)
    (hp : pairingRate hw0 hw1 width (X.mapTime hw0 hw1 width time) Y epsilon ≤ p) :
    RCle (valueNormSq (valueSub
      (I (complexTime hw0 hw1 width time (X.point hw0 hw1 width p))
        (representedTest hw0 hw1 width Y))
      (I (complexTime hw0 hw1 width time (X.limit hw0 hw1 width))
        (representedTest hw0 hw1 width Y))))
      (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  have h := pairing_converges hw0 hw1 width (X.mapTime hw0 hw1 width time)
    Y epsilon he p hp
  rw [PresentedComplexCauchy.mapTime_point, PresentedComplexCauchy.mapTime_limit] at h
  exact h

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexSharpContinuity

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexSharpContinuity.pairing_error_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexSharpContinuity.limit_pairing_error
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexSharpContinuity.pairingTolerance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexSharpContinuity.pairingRate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexSharpContinuity.pairing_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointComplexSharpContinuity.time_pairing_converges
