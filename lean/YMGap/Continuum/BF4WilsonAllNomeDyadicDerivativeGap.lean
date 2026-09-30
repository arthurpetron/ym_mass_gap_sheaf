/-
# The original strict form floor reaches the ACTUAL dyadic derivative

Successive difference quotients have a nonnegative form increment: the
finer root square law identifies it with a squared defect norm. Thus every
quotient dominates the original one-step defect on the input T x. Passing
this inequality through the constructed original pairing limit gives the
same positive core margin for the actual dyadic derivative, without first
identifying it with the regularized logarithm.

The derivative is on the original time range. All-real-time differentiation,
the appropriate closed domain, self-adjointness, physical calibration and
spatial/scaling control remain separate obligations. This is not a physical
Hamiltonian mass gap, and the original nonzero boundary kernel is retained.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative
import YMGap.Continuum.BF4WilsonAllNomeLogCoreGap

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.SU3CharFactor (ofNat_nonneg)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
  (completedInner_sub_right)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics (root_zero_depth)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay
  (defect defectPower defect_symmetric)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit
open YMGap.Continuum.BF4WilsonAllNomeLogCoreGap
  (coreMargin completed_defect_form_gap)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "Q" => differenceQuotient hw0 hw1
local notation "A" => derivativeAction hw0 hw1
local notation "U" => unitState hw0 hw1 width
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (BF4WilsonAllNomeSeminorm.seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

private theorem le_of_sub_nonnegative {a b : RC} (h : RCnonneg (RCsub b a)) : RCle a b := by
  have h' := RCadd_le_add (RCle_refl a) h
  have hz : RCadd a RCzero = a := by
    refine Quotient.inductionOn a ?_
    exact fun A' => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun n => QPoly.q_add_zero_eqv (A'.approx n)))
  have hc : RCadd a (RCsub b a) = b := by
    refine Quotient.inductionOn₂ a b ?_
    intro A' B'
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      RingNormaliser.poly_identity_of_normal_eq
        (.add (.var 0) (.add (.var 1) (.neg (.var 0)))) (.var 1)
        (by decide) (fun | 0 => A'.approx n | _ => B'.approx n)))
  rwa [hz,hc] at h'

/-- Refinement increases the form because its exact difference is a square. -/
theorem quotient_form_step (depth : Nat) (x : V) :
    RCle (B (T 1 x) (Q depth x)) (B (T 1 x) (Q (depth+1) x)) := by
  apply le_of_sub_nonnegative
  rw [← completedInner_sub_right,quotient_step,completedInner_smul_right]
  change RCnonneg (RCscale (Q'.ofNat (2^depth))
    (B (T 1 x) (defect hw0 hw1 (depth+1) (defect hw0 hw1 (depth+1) (T 1 x)))))
  rw [← defect_symmetric]
  have h := RCscale_mono (ofNat_nonneg (2^depth))
    (completedInner_nonnegative hw0 hw1 (defect hw0 hw1 (depth+1) (T 1 x)))
  rwa [RCscale_RCzero] at h

theorem quotient_zero_depth (x : V) :
    Q 0 x = BF4WilsonAllNomeTimeDefectMoments.defect hw0 hw1 (T 1 x) := by
  change completedSmul hw0 hw1 1 (defect hw0 hw1 0 (T 1 x)) = _
  rw [completedSmul_one,defect,root_zero_depth]
  rfl

theorem quotient_form_ge_defect (depth : Nat) (x : V) :
    RCle (B (T 1 x) (BF4WilsonAllNomeTimeDefectMoments.defect hw0 hw1 (T 1 x)))
      (B (T 1 x) (Q depth x)) := by
  induction depth with
  | zero => rw [quotient_zero_depth]; exact RCle_refl _
  | succ depth ih => exact RCle_trans ih (quotient_form_step hw0 hw1 depth x)

/-- The actual derivative limit retains the original defect-form floor. -/
theorem derivative_form_ge_defect (x : V) :
    RCle (B (T 1 x) (BF4WilsonAllNomeTimeDefectMoments.defect hw0 hw1 (T 1 x)))
      (B (T 1 x) (A x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  let TX := (timeNonexpansive hw0 hw1 1).mapCauchy X
  let R := constantRows hw0 hw1 TX
  let S := quotientRows hw0 hw1 X
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro epsilon he
  let n := pairingModulus hw0 hw1 R S epsilon
  have h := (row_pairing_bound hw0 hw1 R S epsilon he n (Nat.le_refl n)).1
  change RCle (B (rowPoint hw0 hw1 R n) (rowPoint hw0 hw1 S n))
    (RCadd (B (limit hw0 hw1 R) (limit hw0 hw1 S)) (rat epsilon)) at h
  rw [constantRows_point,quotientRows_pin,limit_constantRows] at h
  exact RCle_trans (quotient_form_ge_defect hw0 hw1 n (Class X)) h

/-- No margin is lost, but it still depends on the original nome and width. -/
theorem derivative_core_gap (x : V) (hx : B U (T 1 x) = RCzero) :
    RCle (RCscale (coreMargin hw0 hw1 width) (B (T 1 x) (T 1 x)))
      (B (T 1 x) (A x)) :=
  RCle_trans (completed_defect_form_gap hw0 hw1 (T 1 x) hx)
    (derivative_form_ge_defect hw0 hw1 x)

#print axioms quotient_form_step
#print axioms quotient_zero_depth
#print axioms quotient_form_ge_defect
#print axioms derivative_form_ge_defect
#print axioms derivative_core_gap

end YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeGap
