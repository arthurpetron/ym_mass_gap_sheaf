/-
# Laws of the ACTUAL original time derivative

The existing quotient rows converge to J, not to a supplied generator.
The first-order smoothing estimate bounds every quotient by the original
input norm. Original pairing limits prove that J is a positive symmetric
contraction, linear for rational and explicitly QCauchy real scalars,
commutes with T2 and annihilates the original unit.

The exact refinement difference is a positive square when paired with
T2x. Thus B(Jx,T2x) dominates the ORIGINAL transfer-defect form.
This is the next input for a gap on the actual differentiated dense
domain. It does not assert that the unbounded rule H(T2x)=Jx has a
self-adjoint maximal realization, or identify J with the separate
logarithmic candidate. SU(2), nome 1/1024, fixed spacing, T2-time units;
physical normalization, continuum QFT and all-group Clay remain open.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicRealDerivative

namespace YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeLaws

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.SU3CharFactor (ofNat_nonneg)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection (unitCauchy unitCauchy_pin)
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingOrder
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity (smul_norm)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialDifference (smul_zero_state)
open YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial (scale_congr)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional (rc_zero_add)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy (full_mesh_time)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative

local notation "B" => completedInner
local notation "point" X => Quotient.mk seminorm.completionSetoid X

theorem quotient_symmetric (depth : Nat) (x y : Completion) :
    B (differenceQuotient depth x) y=B x (differenceQuotient depth y) := by
  unfold differenceQuotient
  rw [completedInner_smul_left,completedInner_smul_right,
    ← full_mesh_time depth x,← full_mesh_time depth y,
    defect_symmetric,time_symmetric,time_defect]

theorem quotient_nonnegative (depth : Nat) (x : Completion) :
    RCnonneg (B (differenceQuotient depth x) x) := by
  have h := RCscale_mono (ofNat_nonneg (2^depth)) (moment_nonnegative depth x (2^depth) 1)
  rw [RCscale_RCzero] at h
  unfold differenceQuotient
  rw [completedInner_smul_left,defect_symmetric,← full_mesh_time depth x,time_symmetric]
  exact h

/-- The smoothing estimate controls the ACTUAL quotient uniformly in depth. -/
theorem quotient_contraction (depth : Nat) (x : Completion) :
    RCle (B (differenceQuotient depth x) (differenceQuotient depth x)) (B x x) := by
  have h := smoothing_bound depth (2^depth) 1 x
  rw [Nat.one_mul,full_mesh_time] at h
  change RCle (RCscale ((Q'.ofNat (2^depth))^(1+1))
    (B (twoStepTransfer (defect depth x)) (twoStepTransfer (defect depth x)))) (B x x) at h
  have hc : Q'.eqv ((Q'.ofNat (2^depth))^(1+1)) (Q'.ofNat (2^depth)*Q'.ofNat (2^depth)) :=
    Q'.mul_eqv_congr_left _ _ _ (Q'.mul_one_eqv _)
  rw [scale_congr hc,← full_mesh_time depth (defect depth x),time_defect,full_mesh_time] at h
  unfold differenceQuotient
  rw [smul_norm]
  exact h

theorem quotient_transfer (depth : Nat) (x : Completion) :
    differenceQuotient depth (twoStepTransfer x)=twoStepTransfer (differenceQuotient depth x) := by
  unfold differenceQuotient twoStepTransfer
  rw [completedTime_smul]
  apply congrArg (completedSmul (Q'.ofNat (2^depth)))
  change defect depth (twoStepTransfer (twoStepTransfer x))=twoStepTransfer (defect depth (twoStepTransfer x))
  rw [← full_mesh_time depth (twoStepTransfer x),← time_defect,full_mesh_time]

theorem quotient_transfer_nonnegative (depth : Nat) (x : Completion) :
    RCnonneg (B (differenceQuotient depth x) (twoStepTransfer x)) := by
  have h := RCscale_mono (ofNat_nonneg (2^depth)) (defect_positive depth (twoStepTransfer x))
  rw [RCscale_RCzero] at h
  unfold differenceQuotient
  rw [completedInner_smul_left,defect_symmetric]
  exact h

theorem derivative_symmetric (x y : Completion) : B (derivativeAction x) y=B x (derivativeAction y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  have h := rowLimit_pairing_eq (quotientRows X) (constantRows Y) (constantRows X) (quotientRows Y)
    (fun n => quotient_symmetric n (point X) (point Y))
  rw [rowLimit_constant,rowLimit_constant] at h
  exact h

theorem derivative_nonnegative (x : Completion) : RCnonneg (B (derivativeAction x) x) := by
  refine Quotient.inductionOn x ?_
  intro X
  have h := rowLimit_pairing_nonnegative (quotientRows X) (constantRows X)
    (fun n => quotient_nonnegative n (point X))
  rw [rowLimit_constant] at h
  exact h

theorem derivative_contraction (x : Completion) : RCle (B (derivativeAction x) (derivativeAction x)) (B x x) := by
  refine Quotient.inductionOn x ?_
  intro X
  have h := rowLimit_pairing_le (quotientRows X) (quotientRows X) (constantRows X) (constantRows X)
    (fun n => quotient_contraction n (point X))
  rw [rowLimit_constant] at h
  exact h

theorem derivative_add (x y : Completion) :
    derivativeAction (completedAdd x y)=completedAdd (derivativeAction x) (derivativeAction y) := by
  apply completed_eq_of_pairings
  intro z
  rw [derivative_symmetric,completedInner_add_left,completedInner_add_left,
    derivative_symmetric,derivative_symmetric]

theorem derivative_smul (c : Q') (x : Completion) :
    derivativeAction (completedSmul c x)=completedSmul c (derivativeAction x) := by
  apply completed_eq_of_pairings
  intro z
  rw [derivative_symmetric,completedInner_smul_left,completedInner_smul_left,derivative_symmetric]

theorem derivative_realSmul (s : CReal) (cs : QCauchy s.approx) (x : Completion) :
    derivativeAction (completedRealSmul s cs x)=completedRealSmul s cs (derivativeAction x) := by
  apply completed_eq_of_pairings
  intro z
  rw [derivative_symmetric,completedInner_realSmul_left,completedInner_realSmul_left,derivative_symmetric]

theorem derivative_transfer (x : Completion) :
    derivativeAction (twoStepTransfer x)=twoStepTransfer (derivativeAction x) := by
  apply completed_eq_of_pairings
  intro y
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  have h := rowLimit_pairing_eq (quotientRows (timeCauchy 2 X)) (constantRows Y)
    (quotientRows X) (constantRows (timeCauchy 2 Y)) (by
      intro n
      change B (differenceQuotient n (twoStepTransfer (point X))) (point Y)=
        B (differenceQuotient n (point X)) (twoStepTransfer (point Y))
      rw [quotient_transfer,twoStepTransfer_symmetric])
  rw [rowLimit_constant,rowLimit_constant] at h
  rw [twoStepTransfer_symmetric]
  exact h

theorem derivative_transfer_nonnegative (x : Completion) : RCnonneg (B (derivativeAction x) (twoStepTransfer x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  have h := rowLimit_pairing_nonnegative (quotientRows X) (constantRows (timeCauchy 2 X))
    (fun n => quotient_transfer_nonnegative n (point X))
  rw [rowLimit_constant] at h
  exact h

theorem derivative_unit : derivativeAction completedUnit=completedZero := by
  change rowLimit (quotientRows unitCauchy)=completedZero
  apply rowLimit_eq_of_bound _ _ (fun _ => 0)
  intro epsilon he n _
  change RCle (completedDist (differenceQuotient n completedUnit) completedZero) _
  unfold differenceQuotient defect
  rw [twoStepTransfer_unit,generator_unit,completedSub_self,smul_zero_state,
    (completedDist_zero_iff _ _).mpr rfl]
  exact leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_lt he)

/-- Refinement increases the derivative form by a positive original square. -/
theorem quotient_form_step (depth : Nat) (x : Completion) :
    RCle (B (differenceQuotient depth x) (twoStepTransfer x))
      (B (differenceQuotient (depth+1) x) (twoStepTransfer x)) := by
  have hp : RCnonneg (B (completedSub (differenceQuotient (depth+1) x) (differenceQuotient depth x))
      (twoStepTransfer x)) := by
    rw [quotient_step,completedInner_smul_left]
    change RCnonneg (RCscale (Q'.ofNat (2^depth))
      (B (defect (depth+1) (defect (depth+1) (twoStepTransfer x))) (twoStepTransfer x)))
    rw [defect_symmetric]
    have h := RCscale_mono (ofNat_nonneg (2^depth)) (completedInner_nonnegative (defect (depth+1) (twoStepTransfer x)))
    rw [RCscale_RCzero] at h
    exact h
  have h := RCadd_le_add hp (RCle_refl (B (differenceQuotient depth x) (twoStepTransfer x)))
  rw [rc_zero_add,← completedInner_add_left,completedSub_add_cancel] at h
  exact h

theorem quotient_form_lower (depth : Nat) (x : Completion) :
    RCle (B (defect 0 (twoStepTransfer x)) (twoStepTransfer x))
      (B (differenceQuotient depth x) (twoStepTransfer x)) := by
  induction depth with
  | zero =>
      change RCle _ (B (completedSmul 1 (defect 0 (twoStepTransfer x))) (twoStepTransfer x))
      rw [completedSmul_one]
      exact RCle_refl _
  | succ depth ih => exact RCle_trans ih (quotient_form_step depth x)

/-- The ACTUAL derivative dominates the transfer-defect form on its original domain. -/
theorem derivative_form_lower (x : Completion) :
    RCle (B (defect 0 (twoStepTransfer x)) (twoStepTransfer x))
      (B (derivativeAction x) (twoStepTransfer x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  have h := rowLimit_pairing_le (constantRows (quotientRepresentative 0 X)) (constantRows (timeCauchy 2 X))
    (quotientRows X) (constantRows (timeCauchy 2 X)) (by
      intro n
      change RCle (B (differenceQuotient 0 (point X)) (twoStepTransfer (point X)))
        (B (differenceQuotient n (point X)) (twoStepTransfer (point X)))
      change RCle (B (completedSmul 1 (defect 0 (twoStepTransfer (point X)))) _ ) _
      rw [completedSmul_one]
      exact quotient_form_lower n (point X))
  rw [rowLimit_constant,rowLimit_constant,quotientRepresentative_pin] at h
  change RCle (B (completedSmul 1 (defect 0 (twoStepTransfer (point X)))) _ ) _ at h
  rw [completedSmul_one] at h
  exact h

end YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeLaws

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeLaws.quotient_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeLaws.quotient_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeLaws.quotient_contraction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeLaws.quotient_transfer
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeLaws.quotient_transfer_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeLaws.derivative_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeLaws.derivative_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeLaws.derivative_contraction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeLaws.derivative_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeLaws.derivative_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeLaws.derivative_realSmul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeLaws.derivative_transfer
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeLaws.derivative_transfer_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeLaws.derivative_unit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeLaws.quotient_form_step
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeLaws.quotient_form_lower
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeLaws.derivative_form_lower
