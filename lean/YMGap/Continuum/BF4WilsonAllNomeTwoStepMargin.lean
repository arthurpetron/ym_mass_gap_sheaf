/-
# Same-carrier two-step rate margin

On the existing all-nome Wilson completion, a relative loss estimate for one
nonzero vacuum-complement state at lag two forces the certified two-step rate
to be at least `1 - delta`.  This is a calibration/converse theorem: it does
not produce the relative-loss estimate or identify the rate with a physical
Hamiltonian edge.
-/

import YMGap.Continuum.BF4WilsonAllNomeCompletedGap
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap

namespace YMGap.Continuum.BF4WilsonAllNomeTwoStepMargin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap
  (twoStepRate)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedGap
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap
  (leEv_cancel_mul_right_posEv)
open YMGap.Continuum.TuranPositivity (PosEv posEv_of_eventually)

local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat)

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1

def twoStepEnergy (x : V) : RC :=
  RCsub (B x x) (B x (T 2 x))

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

private theorem posEv_two : PosEv (ofQ' (2 : Q')) := by
  exact posEv_of_eventually (ε := (1 : Q')) (by decide) ⟨0, fun n _ => by
    change (1 : Q') ≤ (2 : Q') + 0
    exact by decide⟩

private theorem rc_mul_eq_scale (c : Q') (x : RC) :
    RCmul (Rq c) x = RCscale c x := by
  refine Quotient.inductionOn x ?_
  intro A
  rfl

private theorem rational_scale_cancel_of_floor {a b v : Q'} {X : RC}
    (hv : (0 : Q') < v)
    (hfloor : RCle (Rq v) X)
    (hscaled : RCle (RCscale a X) (RCscale b X)) : a ≤ b := by
  revert hfloor hscaled
  refine Quotient.inductionOn X ?_
  intro A hfloor hscaled
  have hc : leEv (ofQ' a) (ofQ' b) :=
    leEv_cancel_mul_right_posEv ⟨v, hv, hfloor⟩
      (by
        rw [RCscale_mk, RCscale_mk] at hscaled
        change leEv (mul (ofQ' a) A) (mul (ofQ' b) A) at hscaled
        exact hscaled)
  exact GNSQuotient.GNSData.RCofQ'_le_reflect hc

private theorem rate_margin_from_relative_energy
    (x : VacuumComplement hw0 hw1 (width := width)) (delta v : Q')
    (hv : (0 : Q') < v)
    (hfloor : RCle (Rq v) (B x.val x.val))
    (henergy : RCle (twoStepEnergy hw0 hw1 width x.val)
      (RCscale delta (B x.val x.val))) :
    1 - delta ≤ twoStepRate hw0 hw1 width := by
  have hlower := response_lower delta (B x.val x.val)
    (B x.val (T 2 x.val)) henergy
  have hupper := vacuumComplement_twoStep_form_gap hw0 hw1 width x
  rw [rc_mul_eq_scale] at hupper
  exact rational_scale_cancel_of_floor hv hfloor
    (RCle_trans hlower hupper)

theorem vacuumComplement_twoStep_rate_margin
    (x : VacuumComplement hw0 hw1 (width := width)) (delta v : Q')
    (hv : (0 : Q') < v)
    (hfloor : RCle (Rq v) (B x.val x.val))
    (henergy : RCle (twoStepEnergy hw0 hw1 width x.val)
      (RCscale delta (B x.val x.val))) :
    1 - delta ≤ twoStepRate hw0 hw1 width :=
  rate_margin_from_relative_energy hw0 hw1 width x delta v hv hfloor henergy

theorem vacuumComplement_twoStep_margin_le_relative_energy
    (x : VacuumComplement hw0 hw1 (width := width)) (delta v : Q')
    (hv : (0 : Q') < v)
    (hfloor : RCle (Rq v) (B x.val x.val))
    (henergy : RCle (twoStepEnergy hw0 hw1 width x.val)
      (RCscale delta (B x.val x.val))) :
    1 + -(twoStepRate hw0 hw1 width) ≤ delta := by
  have h := Q'.le_add_of_sub_le
    (rate_margin_from_relative_energy hw0 hw1 width x delta v hv hfloor henergy)
  exact Q'.sub_le_of_le_add (Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

#print axioms twoStepEnergy
#print axioms vacuumComplement_twoStep_rate_margin
#print axioms vacuumComplement_twoStep_margin_le_relative_energy

end YMGap.Continuum.BF4WilsonAllNomeTwoStepMargin
