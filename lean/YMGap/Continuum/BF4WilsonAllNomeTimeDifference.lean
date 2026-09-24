/-
# Quantitative nonvanishing of the all-nome two-step difference

On the SAME completed vacuum complement, the existing strict two-step form
bound forces `x-T²x` to retain at least `(1-q)²` of the squared norm of `x`. The
proof is the exact completed quadratic identity with a positive residual and
the nonnegative gap remainder.  No division, real scalar extension, or
changing-parameter claim is used.
-/

import YMGap.Continuum.BF4WilsonAllNomeBilinearTime
import YMGap.Continuum.BF4WilsonAllNomeLinearLaws
import YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation

namespace YMGap.Continuum.BF4WilsonAllNomeTimeDifference

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedGap
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap
  (twoStepRate twoStepRate_lt_one)
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation
  (plaquetteExcitation plaquetteExcitation_norm_floor originFace originFace_mem)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio starRatio_positive)
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "U" => unitState hw0 hw1 width
local notation "q" => twoStepRate hw0 hw1 width

private theorem rc_negative_one (a : RC) : RCscale (-1) a = RCneg a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 (A.approx n))
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv (A.approx n)))))

private theorem completedInner_sub_left (x y z : V) :
    B (completedSub hw0 hw1 x y) z = RCsub (B x z) (B y z) := by
  unfold completedSub completedNeg RCsub
  rw [completedInner_add_left, completedInner_smul_left, rc_negative_one]

private theorem completedInner_sub_right (x y z : V) :
    B x (completedSub hw0 hw1 y z) = RCsub (B x y) (B x z) := by
  rw [completedInner_symm hw0 hw1 x, completedInner_sub_left,
    completedInner_symm hw0 hw1 y x, completedInner_symm hw0 hw1 z x]

private theorem rcscale_as_mul (c : Q') (a : RC) :
    RCscale c a = RCmul (Quotient.mk crealSetoid (ofQ' c)) a := by
  refine Quotient.inductionOn a ?_
  intro A
  rfl

private theorem rc_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.add_neg_self_eqv _))

private theorem rc_sub_nonnegative_of_le {a b : RC} (h : RCle b a) :
    RCnonneg (RCsub a b) := by
  have h' := RCadd_le_add h (RCle_refl (RCneg b))
  change RCle (RCsub b b) (RCsub a b) at h'
  rwa [rc_sub_self] at h'

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_add_zero_eqv _))

private theorem rc_le_add_nonnegative (a b : RC) (hb : RCnonneg b) :
    RCle a (RCadd a b) := by
  have h := RCadd_le_add (RCle_refl a) hb
  rwa [rc_add_zero] at h

private theorem quadratic_identity (rate : Q') (a b c : RC) :
    RCsub (RCsub a b) (RCsub b c) =
      RCadd (RCscale ((1-rate)*(1-rate)) a)
        (RCadd
          (RCsub (RCsub c (RCscale rate b))
            (RCscale rate (RCsub b (RCscale rate a))))
          (RCscale (2*(1-rate)) (RCsub (RCscale rate a) b))) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A' B' C'
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.var 1)))
      (.neg (.add (.var 1) (.neg (.var 2)))))
    (.add
      (.mul (.mul (.add (.const 1) (.neg (.var 3)))
        (.add (.const 1) (.neg (.var 3)))) (.var 0))
      (.add
        (.add
          (.add (.var 2) (.neg (.mul (.var 3) (.var 1))))
          (.neg (.mul (.var 3)
            (.add (.var 1) (.neg (.mul (.var 3) (.var 0)))))))
        (.mul (.mul (.const 2) (.add (.const 1) (.neg (.var 3))))
          (.add (.mul (.var 3) (.var 0)) (.neg (.var 1))))))
    (by decide)
    (fun | 0 => A'.approx n | 1 => B'.approx n | 2 => C'.approx n | _ => rate)

/-- The actual completed two-step difference. -/
def timeDifference (x : V) : V := completedSub hw0 hw1 x (T 2 x)

/-- A strict form bound gives a quantitative norm floor for the actual
two-step difference on the SAME vacuum-complement state. -/
theorem timeDifference_norm_lower (x : V) (hx : B U x = RCzero) :
    RCle (RCscale ((1-q)*(1-q)) (B x x))
      (B (timeDifference hw0 hw1 x) (timeDifference hw0 hw1 x)) := by
  let y := T 2 x
  let r := completedSub hw0 hw1 y (S q x)
  have hgap := completed_twoStep_form_gap hw0 hw1 width x
    ((completedInner_symm hw0 hw1 x U).trans hx)
  rw [← rcscale_as_mul q (B x x)] at hgap
  have hrem : RCnonneg (RCsub (RCscale q (B x x)) (B x y)) := by
    exact rc_sub_nonnegative_of_le hgap
  have hcoef : (0 : Q') ≤ 2*(1-q) := by
    exact Q'.mul_nonneg _ _ (by decide)
      (Q'.sub_nonneg_of_le (Q'.le_of_lt (twoStepRate_lt_one hw0 hw1 width)))
  have hscaled : RCnonneg
      (RCscale (2*(1-q)) (RCsub (RCscale q (B x x)) (B x y))) := by
    have h := RCscale_mono hcoef hrem
    rw [RCscale_RCzero] at h
    exact h
  have hr : RCnonneg (B r r) := completedInner_nonnegative hw0 hw1 r
  have htail : RCnonneg
      (RCadd (B r r)
        (RCscale (2*(1-q)) (RCsub (RCscale q (B x x)) (B x y)))) :=
    RCadd_le_add hr hscaled
  have hid : B (timeDifference hw0 hw1 x) (timeDifference hw0 hw1 x) =
      RCadd (RCscale ((1-q)*(1-q)) (B x x))
        (RCadd (B r r)
          (RCscale (2*(1-q)) (RCsub (RCscale q (B x x)) (B x y)))) := by
    change B (completedSub hw0 hw1 x y) (completedSub hw0 hw1 x y) = _
    dsimp only [r]
    simp only [completedInner_sub_left, completedInner_sub_right,
      completedInner_smul_right, completedInner_smul_left,
      completedInner_symm hw0 hw1 y x]
    exact quadratic_identity q (B x x) (B x y) (B y y)
  rw [hid]
  exact rc_le_add_nonnegative _ _ htail

/-- The constructed difference remains in the SAME orthogonal sector. -/
theorem timeDifference_orthogonal (x : V) (hx : B U x = RCzero) :
    B U (timeDifference hw0 hw1 x) = RCzero := by
  unfold timeDifference
  rw [completedInner_sub_right,
    completedTime_preserves_vacuumComplement hw0 hw1 2 x hx, hx, rc_sub_self]

def timeDifferenceExcitation (x : VacuumComplement hw0 hw1 (width := width)) :
    VacuumComplement hw0 hw1 (width := width) :=
  ⟨timeDifference hw0 hw1 x.val, timeDifference_orthogonal hw0 hw1 x.val x.property⟩

/-- Computed positive norm floor, with nome AND width dependence retained. -/
def differenceFloor (width : Nat) : Q' :=
  let rate := twoStepRate hw0 hw1 width
  ((1-rate)*(1-rate))*starRatio w

theorem differenceFloor_positive (width : Nat) :
    (0 : Q') < differenceFloor hw0 hw1 width := by
  have h := HKPos.one_sub_pos (twoStepRate_lt_one hw0 hw1 width)
  exact Q'.mul_pos (Q'.mul_pos h h) (starRatio_positive hw0 hw1)

theorem plaquetteTimeDifference_norm_floor (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) :
    let state := timeDifferenceExcitation hw0 hw1 (plaquetteExcitation hw0 hw1 width face hf)
    RCle (Quotient.mk crealSetoid (ofQ' (differenceFloor hw0 hw1 width)))
      (B state.val state.val) := by
  let state := plaquetteExcitation hw0 hw1 width face hf
  exact RCle_trans
    (RCscale_mono (SumOfSquares.q_mul_self_nonneg (1-twoStepRate hw0 hw1 width))
      (plaquetteExcitation_norm_floor hw0 hw1 width face hf))
    (timeDifference_norm_lower hw0 hw1 state.val state.property)

/-- Every positive width has an actual time-difference excitation and a
positive rational norm floor. This is not changing-scale survival. -/
def positiveTimeDifferenceExcitation (width : Nat) :
    Σ state : VacuumComplement hw0 hw1 (width := width+1),
      {floor : Q' // (0 : Q') < floor ∧
        RCle (Quotient.mk crealSetoid (ofQ' floor)) (B state.val state.val)} :=
  ⟨timeDifferenceExcitation hw0 hw1
      (plaquetteExcitation hw0 hw1 (width+1) originFace (originFace_mem width)),
    differenceFloor hw0 hw1 (width+1), differenceFloor_positive hw0 hw1 (width+1),
    plaquetteTimeDifference_norm_floor hw0 hw1 (width+1) originFace (originFace_mem width)⟩

#print axioms timeDifference
#print axioms timeDifference_norm_lower
#print axioms timeDifference_orthogonal
#print axioms timeDifferenceExcitation
#print axioms differenceFloor
#print axioms differenceFloor_positive
#print axioms plaquetteTimeDifference_norm_floor
#print axioms positiveTimeDifferenceExcitation

end YMGap.Continuum.BF4WilsonAllNomeTimeDifference
