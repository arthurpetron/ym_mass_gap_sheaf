/-
# Two-sided strict response of the same completed physical excitation

The existing excitation d=T root-root already has a positive norm floor
and positive Rayleigh deficit. The full-space mixed test inequality now
supplies a positive transfer-response floor from its original probe pairing.
Both bounds are converted to relative rational rates for THIS vector.

No common rate for all vectors, unit-normalized canonical OS probe,
geometric time, vacuum uniqueness or continuum gap is asserted.
-/

import YMGap.Continuum.BF4PhysicalCubeMixedTestBound
import YMGap.Continuum.BF4PhysicalCubeStrictExcitation

namespace YMGap.Continuum.BF4PhysicalCubeExcitationResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ScaledGNSCompletionEstimates
open YMGap.Continuum.BF4PhysicalCubeReflectedCompletion
open YMGap.Continuum.BF4PhysicalCubeCompletedTransfer
open YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws
open YMGap.Continuum.BF4PhysicalCubeSectorVacuumNorm
open YMGap.Continuum.BF4PhysicalCubeDissipation
open YMGap.Continuum.BF4PhysicalCubeMixedTestBound
open YMGap.Continuum.BF4PhysicalCubeStrictExcitation
open YMGap.Continuum.BF4PhysicalCubeTransferNonidentity
open YMGap.Continuum.BF4PhysicalCubeTwoStepPositivePairing

local notation "B" => cubeReflectedInner
local notation "T" => cubeTransfer
local notation "d" => excitation.val
local notation "U" => excitationNormCeiling

def responseFloor : Q' :=
  Q'.divPos (twoStepFloor * twoStepFloor) (marginalCeiling probeVector) (marginalCeiling_pos probeVector)

theorem responseFloor_pos : (0 : Q') < responseFloor :=
  Q'.divPos_pos _ _ _ (Q'.mul_pos twoStepFloor_pos twoStepFloor_pos)

theorem excitation_response_floor : RCle (Rq responseFloor) (B (T d) d) :=
  response_floor_of_test d probeVector twoStepFloor (Q'.le_of_lt twoStepFloor_pos) excitation_probe_floor

def lowerRate : Q' := Q'.divPos responseFloor U excitationNormCeiling_pos
def relativeDeficit : Q' := Q'.divPos excitationDeficitFloor U excitationNormCeiling_pos
def upperRate : Q' := 1 + -relativeDeficit

theorem lowerRate_pos : (0 : Q') < lowerRate := Q'.divPos_pos _ _ _ responseFloor_pos
theorem relativeDeficit_pos : (0 : Q') < relativeDeficit := Q'.divPos_pos _ _ _ excitationDeficitFloor_pos

private theorem one_sub_lt_one (r : Q') (hr : (0 : Q') < r) : 1 + -r < (1 : Q') := by
  have hn := Q'.num_pos_of_pos hr
  show (1 + -r).num * ((1 : Q').den : Int) < (1 : Q').num * ((1 + -r).den : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.neg_den]
  change (1 * (r.den : Int) + -r.num * 1) * 1 < 1 * (1 * (r.den : Int))
  simp only [Int.one_mul, Int.mul_one]
  omega

theorem upperRate_lt_one : upperRate < (1 : Q') := one_sub_lt_one _ relativeDeficit_pos

/-- Paying a relative floor uses the known positive rational norm ceiling,
not a division by the vector's constructive-real norm. -/
private theorem relative_norm_le (floor : Q') (hfloor : (0 : Q') ≤ floor) :
    RCle (RCmul (Rq (Q'.divPos floor U excitationNormCeiling_pos)) (B d d)) (Rq floor) := by
  have hr : (0 : Q') ≤ Q'.divPos floor U excitationNormCeiling_pos :=
    Q'.mul_nonneg _ _ hfloor (Q'.le_of_lt (Q'.recipPos_pos _ _))
  have h := mul_mono_left (rq_nonnegative hr) excitation_norm_ceiling
  rwa [rq_mul, rq_eqv (Q'.divPos_mul_eqv _ _ _)] at h

theorem excitation_relative_lower : RCle (RCmul (Rq lowerRate) (B d d)) (B (T d) d) :=
  RCle_trans (relative_norm_le responseFloor (Q'.le_of_lt responseFloor_pos)) excitation_response_floor

private theorem add_sub_cancel (a b : RC) : RCadd (RCadd a b) (RCneg b) = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  apply Quotient.sound
  exact SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv _ _ _) (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv _))
      (Q'.eqv_of_eq (Q'.add_zero' _))))

private theorem relative_complement (a : RC) (r : Q') :
    RCadd a (RCneg (RCmul (Rq r) a)) = RCmul (Rq (1 + -r)) a := by
  refine Quotient.inductionOn a ?_
  intro A
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  change Q'.eqv (A.approx n + -(r * A.approx n)) ((1 + -r) * A.approx n)
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
    (Q'.add_eqv_congr' (Q'.one_mul_eqv _) (Q'.neg_mul_eqv _ _)))

theorem excitation_relative_upper : RCle (B (T d) d) (RCmul (Rq upperRate) (B d d)) := by
  have h := RCle_trans (RCadd_le_add (RCle_refl (B (T d) d))
    (relative_norm_le excitationDeficitFloor (Q'.le_of_lt excitationDeficitFloor_pos)))
    excitation_strict_form
  change RCle (RCadd (B (T d) d) (RCmul (Rq relativeDeficit) (B d d))) (B d d) at h
  have hsub := RCadd_le_add h (RCle_refl (RCneg (RCmul (Rq relativeDeficit) (B d d))))
  rw [add_sub_cancel, relative_complement] at hsub
  exact hsub

/-- One actual centered vector has positive response and a strict upper
relative rate. Neither rate is asserted valid for any other vector. -/
theorem excitation_two_sided_response :
    RCle (RCmul (Rq lowerRate) (B d d)) (B (T d) d) ∧
      RCle (B (T d) d) (RCmul (Rq upperRate) (B d d)) :=
  ⟨excitation_relative_lower, excitation_relative_upper⟩

theorem excitation_transfer_ne_zero : T d ≠ cubeReflectedEmbed [] :=
  fun h => excitation_ne_zero (transfer_kernel_trivial d h)

end YMGap.Continuum.BF4PhysicalCubeExcitationResponse

#print axioms YMGap.Continuum.BF4PhysicalCubeExcitationResponse.responseFloor
#print axioms YMGap.Continuum.BF4PhysicalCubeExcitationResponse.responseFloor_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeExcitationResponse.excitation_response_floor
#print axioms YMGap.Continuum.BF4PhysicalCubeExcitationResponse.lowerRate
#print axioms YMGap.Continuum.BF4PhysicalCubeExcitationResponse.relativeDeficit
#print axioms YMGap.Continuum.BF4PhysicalCubeExcitationResponse.upperRate
#print axioms YMGap.Continuum.BF4PhysicalCubeExcitationResponse.lowerRate_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeExcitationResponse.relativeDeficit_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeExcitationResponse.upperRate_lt_one
#print axioms YMGap.Continuum.BF4PhysicalCubeExcitationResponse.excitation_relative_lower
#print axioms YMGap.Continuum.BF4PhysicalCubeExcitationResponse.excitation_relative_upper
#print axioms YMGap.Continuum.BF4PhysicalCubeExcitationResponse.excitation_two_sided_response
#print axioms YMGap.Continuum.BF4PhysicalCubeExcitationResponse.excitation_transfer_ne_zero
