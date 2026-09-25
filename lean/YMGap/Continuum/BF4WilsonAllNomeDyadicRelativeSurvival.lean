/-
# Same-carrier dyadic relative-energy survival

The literal padded dyadic square already has a completed norm floor and an
absolute centered loss estimate.  This file joins them through an explicit
relative-loss budget and returns a positive response for that SAME completed
state.  The budget is deliberately a hypothesis: the existing cubic loss
bound has not been shown to satisfy it along a changing-scale trajectory.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicExcitation
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicRelativeSurvival

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4DyadicWilsonSquare (side)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap
  (twoStepRate)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
  (starRatio starRatio_positive)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeDyadicExcitation
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap
  (leEv_cancel_mul_right_posEv)
open YMGap.Continuum.TuranPositivity (PosEv posEv_of_eventually)

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (scale width : Nat) (hwidth : side scale < width)

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "v" => Subtype.val
  (dyadicExcitation hw0 hw1 scale width hwidth)

def dyadicEnergy : RC :=
  RCsub (B v v) (B v (T (side scale) v))

def dyadicLossBound : Q' :=
  (384 : Q') * (Q'.ofNat (side scale) *
    (Q'.ofNat (side scale) * Q'.ofNat (side scale))) * (1 + -w)

private theorem response_lower (r : Q') (norm response : RC)
    (h : RCle (RCsub norm response) (RCscale r norm)) :
    RCle (RCscale (1-r) norm) response := by
  revert h
  refine Quotient.inductionOn₂ norm response ?_
  intro N F h epsilon he
  obtain ⟨index, hN⟩ := h epsilon he
  refine ⟨index, fun k hk => ?_⟩
  have hneg := Q'.add_le_add_left (N.approx k) _ _
    (Q'.neg_le_neg_add (hN k hk))
  change (1-r)*N.approx k ≤ F.approx k + epsilon
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (YMGap.Continuum.RingNormaliser.poly_identity_of_normal_eq
      (.mul (.add (.const 1) (.neg (.var 0))) (.var 1))
      (.add (.var 1) (.neg (.mul (.var 0) (.var 1)))) (by decide)
      (fun | 0 => r | _ => N.approx k)))
    (Q'.le_trans' _ _ _ hneg (Q'.le_of_eqv
      (YMGap.Continuum.RingNormaliser.poly_identity_of_normal_eq
        (.add (.var 0) (.add (.neg (.add (.var 0) (.neg (.var 1)))) (.var 2)))
        (.add (.var 1) (.var 2)) (by decide)
        (fun | 0 => N.approx k | 1 => F.approx k | _ => epsilon))))

private theorem remaining_fraction {r theta : Q'} (h : r+theta ≤ (1 : Q')) :
    theta ≤ 1-r := by
  have h' := Q'.add_le_add_right _ _ (-r) h
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv
    (YMGap.Continuum.RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
      (by decide) (fun | 0 => r | _ => theta))) h'

private theorem scale_rational (c q : Q') :
    RCscale c (Rq q) = Rq (c*q) := by
  rw [RCscale_mk]
  exact Quotient.sound (CRealAlg.ofQ'_mul c q).symm

private theorem rc_mul_eq_scale (c : Q') (x : RC) :
    RCmul (Rq c) x = RCscale c x := by
  refine Quotient.inductionOn x ?_
  intro A
  rfl

private theorem posEv_two : PosEv (ofQ' (2 : Q')) := by
  exact posEv_of_eventually (ε := (1 : Q')) (by decide) ⟨0, fun n _ => by
    change (1 : Q') ≤ (2 : Q') + 0
    exact by decide⟩

private theorem rcscale_cancel_two {a b : RC}
    (h : RCle (RCscale (2 : Q') a) (RCscale (2 : Q') b)) :
    RCle a b := by
  revert h
  refine Quotient.inductionOn₂ a b ?_
  intro xA xB h
  change leEv (mul (ofQ' (2 : Q')) xA) (mul (ofQ' (2 : Q')) xB) at h
  have h' := (leEv_congr (CRealAlg.cmul_comm _ _)
    (CRealAlg.cmul_comm _ _)).mp h
  exact leEv_cancel_mul_right_posEv posEv_two h'

/- The direct same-carrier compiler.  Its only analytic input is a relative
   loss estimate for the actual dyadic state at its own discrete lag. -/
theorem dyadic_response_ge_fraction_of_relative_energy
    (delta theta : Q')
    (hbudget : delta + theta ≤ (1 : Q'))
    (henergy : RCle (dyadicEnergy hw0 hw1 scale width hwidth)
      (RCscale delta (B v v))) :
    RCle (RCscale theta (B v v)) (B v (T (side scale) v)) := by
  have hremaining := remaining_fraction hbudget
  exact RCle_trans
    (RCscale_scalar_mono hremaining
      (completedInner_nonnegative hw0 hw1 v))
    (response_lower delta (B v v) (B v (T (side scale) v)) henergy)

/- The norm floor is consumed on the SAME dyadic excitation, producing a
   positive rational response floor without selecting a new representative. -/
theorem dyadic_response_floor_of_relative_energy
    (delta theta : Q')
    (htheta : (0 : Q') ≤ theta)
    (hbudget : delta + theta ≤ (1 : Q'))
    (henergy : RCle (dyadicEnergy hw0 hw1 scale width hwidth)
      (RCscale delta (B v v))) :
    RCle (Rq (theta * starRatio w)) (B v (T (side scale) v)) := by
  have hfloor := dyadicExcitation_norm_floor hw0 hw1 scale width hwidth
  have hscaled := RCscale_mono htheta hfloor
  rw [scale_rational] at hscaled
  exact RCle_trans hscaled
    (dyadic_response_ge_fraction_of_relative_energy hw0 hw1 scale width hwidth
      delta theta hbudget henergy)

/- The existing absolute cubic loss estimate can now feed the compiler when an
   explicit SAME-norm budget pays its factor of two. -/
theorem dyadic_relative_energy_of_loss_budget
    (delta : Q')
    (hbudgetLoss : RCle (Rq (dyadicLossBound (w := w) scale))
      (RCscale (2*delta) (B v v))) :
    RCle (dyadicEnergy hw0 hw1 scale width hwidth)
      (RCscale delta (B v v)) := by
  have hloss := centered_dyadic_loss_bound hw0 hw1 scale width hwidth
  dsimp [dyadicEnergy, dyadicLossBound]
  dsimp only at hloss
  have hcombined := RCle_trans hloss hbudgetLoss
  rw [rc_mul_eq_scale] at hcombined
  rw [← RCscale_RCscale] at hcombined
  exact rcscale_cancel_two hcombined

theorem dyadic_response_floor_of_loss_budget
    (delta theta : Q')
    (htheta : (0 : Q') ≤ theta)
    (hbudget : delta + theta ≤ (1 : Q'))
    (hbudgetLoss : RCle (Rq (dyadicLossBound (w := w) scale))
      (RCscale (2*delta) (B v v))) :
    RCle (Rq (theta * starRatio w)) (B v (T (side scale) v)) := by
  exact dyadic_response_floor_of_relative_energy hw0 hw1 scale width hwidth
    delta theta htheta hbudget
    (dyadic_relative_energy_of_loss_budget hw0 hw1 scale width hwidth delta
      hbudgetLoss)

#print axioms dyadicEnergy
#print axioms dyadicLossBound
#print axioms dyadic_response_ge_fraction_of_relative_energy
#print axioms dyadic_response_floor_of_relative_energy
#print axioms dyadic_relative_energy_of_loss_budget
#print axioms dyadic_response_floor_of_loss_budget

end YMGap.Continuum.BF4WilsonAllNomeDyadicRelativeSurvival
