/-
# Necessary strength of the SAME completed signed gain

For the existing original completed transfer, write C_k=<x,T^k x>.
Its positive time defect gives C_(k+1)<=C_k. Consequently, for a>=0,

  C_(k+1)-a*C_k <= (1-a)*C_(k+1).

If C_(k+1) has an explicit positive rational floor and the actual signed
gain is at least gamma*C_(k+1), then gamma<=1-a. Cancellation uses only
eventual order and the supplied floor, not a real inverse or a spectrum.

This is a necessary constraint on extending the actual fixed bent-loop
gain producer. In particular a fixed quarter-gain estimate cannot be
continued to reference coefficients approaching one on positive responses.
No assertion that a growing-loop reference approaches one, no analytic
gain production and no changing-family or continuum theorem is made here.
-/

import YMGap.Continuum.BF4WilsonAllNomeTimeDefectTail
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap
import YMGap.Continuum.RCSignedPairBudget

namespace YMGap.Continuum.BF4WilsonAllNomeGainStrengthConstraint

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (mixedMoment defectPower)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectTail (mixedMoment_time_decreasing)
open YMGap.Continuum.RCSignedPairBudget (neg_mono)
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap
  (leEv_cancel_mul_right_posEv)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "Rq" q:arg => Quotient.mk crealSetoid (ofQ' q)

theorem response_time_decreasing (x : V) (k : Nat) :
    RCle (B x (T (k+1) x)) (B x (T k x)) := by
  simpa only [mixedMoment, defectPower] using
    mixedMoment_time_decreasing hw0 hw1 x k 0

private theorem sub_self_scale (a : Q') (x : RC) :
    RCsub x (RCscale a x) = RCscale (1-a) x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
      (Q'.add_eqv_congr' (Q'.one_mul_eqv (X.approx n))
        (Q'.neg_mul_eqv a (X.approx n))))))

/-- An upper bound for the actual signed gain, on the original time map. -/
theorem signed_gain_upper (x : V) (k : Nat) (a : Q') (ha : (0 : Q') ≤ a) :
    RCle (RCsub (B x (T (k+1) x)) (RCscale a (B x (T k x))))
      (RCscale (1-a) (B x (T (k+1) x))) := by
  have h := RCadd_le_add (RCle_refl (B x (T (k+1) x)))
    (neg_mono (RCscale_mono ha (response_time_decreasing hw0 hw1 x k)))
  change RCle _ (RCsub (B x (T (k+1) x))
    (RCscale a (B x (T (k+1) x)))) at h
  rwa [sub_self_scale] at h

private theorem cancel_scale {X : RC} (floor : Q') (hfloor0 : (0 : Q') < floor)
    (hfloor : RCle (Rq floor) X) (a b : Q')
    (h : RCle (RCscale a X) (RCscale b X)) : a ≤ b := by
  revert hfloor h
  refine Quotient.inductionOn X ?_
  intro Y hfloor h
  have hc := leEv_cancel_mul_right_posEv ⟨floor, hfloor0, hfloor⟩ h
  exact GNSQuotient.GNSData.RCofQ'_le_reflect hc

/-- The unpaid deficit to the gain ceiling is exactly the response drop,
scaled by the SAME reference. This identifies the stronger scaling target. -/
theorem signed_gain_ceiling_deficit (x : V) (k : Nat) (a : Q') :
    RCsub (RCscale (1-a) (B x (T (k+1) x)))
      (RCsub (B x (T (k+1) x)) (RCscale a (B x (T k x)))) =
    RCscale a (RCsub (B x (T k x)) (B x (T (k+1) x))) := by
  generalize B x (T (k+1) x) = S, B x (T k x) = P
  refine Quotient.inductionOn₂ S P ?_
  intro X Y
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.add (.const 1) (.neg (.var 0))) (.var 1))
        (.neg (.add (.var 1) (.neg (.mul (.var 0) (.var 2))))))
      (.mul (.var 0) (.add (.var 2) (.neg (.var 1))))
      (by decide) (fun | 0 => a | 1 => X.approx n | _ => Y.approx n)))

/-- Any relative gain producer on a positive response must obey this
constraint. The floor belongs to the SAME next response, not a Haar norm. -/
theorem signed_gain_strength_constraint (x : V) (k : Nat) (a gamma floor : Q')
    (ha : (0 : Q') ≤ a) (hfloor0 : (0 : Q') < floor)
    (hfloor : RCle (Rq floor) (B x (T (k+1) x)))
    (hgain : RCle (RCscale gamma (B x (T (k+1) x)))
      (RCsub (B x (T (k+1) x)) (RCscale a (B x (T k x))))) :
    gamma ≤ 1-a :=
  cancel_scale floor hfloor0 hfloor gamma (1-a)
    (RCle_trans hgain (signed_gain_upper hw0 hw1 x k a ha))

#print axioms response_time_decreasing
#print axioms signed_gain_upper
#print axioms signed_gain_ceiling_deficit
#print axioms signed_gain_strength_constraint

end YMGap.Continuum.BF4WilsonAllNomeGainStrengthConstraint
