/-
# A nonzero exactly centered source on the SAME Wilson completion

The origin p01-minus-p02 source has zero ORIGINAL mean at every finite
chronological stage. Its existing joint limit and intrinsic unit pairing
therefore vanish. The raw embedded source belongs to the existing vacuum
complement, and its centered time moments equal its raw completed pairings.
The existing signed-family coercivity supplies norm squared at least
2*varianceFloor(w)>0 at each fixed strict nome and width>=1.

This removes moving-center debt, not signed interacting cost. The floor
deteriorates with nome; no positive-time survival, slow-rate estimate,
changing-family control, continuum excitation or physical gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialAntisymmetricPlaquette
import YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyVariance
import YMGap.Continuum.BF4WilsonJointFunctionalLaws
import YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion

namespace YMGap.Continuum.BF4WilsonAllNomeAntisymmetricPlaquette

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialAntisymmetricPlaquette
open YMGap.Continuum.BF4WilsonPlaquetteFamilySourcePin (familyState)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra (zero smul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm (sum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette (plaquetteLoop)
open YMGap.Continuum.BF4ExactSlabSpatialAxisSwapWilsonLoop (swapSourceLoop)
open YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapForm (swapIntrinsic)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance advance_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit (originalWindowScalar)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
  (originalJointLimit originalJoint_diagonal_converges)
open YMGap.Continuum.BF4WilsonJointFunctionalLaws (joint_congr equiv_sub)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm (intrinsicForm intrinsicForm_symm)
open YMGap.Continuum.BF4WilsonAllNomeFormLaws (intrinsicForm_zero_left)
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments (centeredTimeMoment)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeSpatialAxisSwapCompletion
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
  (completedTime completedTime_embed VacuumComplement)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteFamilyVariance (centered_norm_floor)
open YMGap.Continuum.BF4ExactSlabPlaquetteAffineCoercivity (varianceFloor varianceFloor_positive)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

/-- The actual radius-zero family state, not a replacement completion. -/
def state {width : Nat} (hw : 1 ≤ width) : IntrinsicExpression width :=
  familyState width faces coefficient (faces_physical hw)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  {width : Nat} (hw : 1 ≤ width)

attribute [local irreducible] originalJointLimit originalWindowScalar

/-- Zero means pass through the already chosen original diagonal limit. -/
theorem joint_mean_zero :
    Equiv (originalJointLimit hw0 hw1 0 (expression hw) (expression_within hw)) czero := by
  apply Equiv_of_limit_of_equal
    (aSeq := fun stage => ofQ' (originalWindowScalar hw0 hw1 0
      (expression hw) stage stage stage)) (bSeq := fun _ => czero) ?_
    (originalJoint_diagonal_converges hw0 hw1 0 (expression hw) (expression_within hw))
    (convergesTo_const czero)
  intro stage
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ =>
    original_mean_zero hw0 hw1 hw 0 stage stage stage)

/-- The SAME intrinsic reflected pairing, including its original partition. -/
theorem state_mean_zero :
    Equiv (intrinsicForm hw0 hw1 (state hw) (unit width)) czero := by
  change Equiv (originalJointLimit hw0 hw1 0 (.mul (expression hw) .one) _) czero
  exact (joint_congr hw0 hw1 0 (.mul (expression hw) .one) (expression hw)
    ⟨expression_within hw, True.intro⟩ (expression_within hw)
    (RatPolyCoeffEqv.mul_one _)).trans (joint_mean_zero hw0 hw1 hw)

theorem state_mean_left_zero :
    Equiv (intrinsicForm hw0 hw1 (unit width) (state hw)) czero :=
  (intrinsicForm_symm hw0 hw1 (unit width) (state hw)).trans (state_mean_zero hw0 hw1 hw)

/-- Centering changes no time moment for this produced source. This is not
a decay or positive-time lower bound. -/
theorem centeredMoment_uncentered (n : Nat) :
    Equiv (centeredTimeMoment hw0 hw1 n (state hw) (state hw))
      (intrinsicForm hw0 hw1 (state hw) (advance n (state hw))) := by
  unfold centeredTimeMoment
  exact (equiv_sub (Equiv.refl _)
    (Pivot2.mul_congr_left (state_mean_zero hw0 hw1 hw))).trans
    (SumOfSquares.Equiv_of_approx_eqv (fun k =>
      poly_identity_of_normal_eq
        (.add (.var 0) (.neg (.mul (.const 0) (.var 1)))) (.var 0) (by decide)
        (fun
          | 0 => (intrinsicForm hw0 hw1 (state hw) (advance n (state hw))).approx k
          | _ => (intrinsicForm hw0 hw1 (unit width) (state hw)).approx k)))

/-- Raw embedding with proved orthogonality; no real centering coefficient
or representative choice is needed. -/
def excitation : VacuumComplement hw0 hw1 (width := width) :=
  ⟨embed hw0 hw1 (state hw), by
    change completedInner hw0 hw1 (embed hw0 hw1 (unit width))
      (embed hw0 hw1 (state hw)) = RCzero
    rw [completedInner_embed]
    exact Quotient.sound (state_mean_left_zero hw0 hw1 hw)⟩

/-- The original signed-family floor with its literal two-face budget. -/
theorem state_norm_floor :
    leEv (ofQ' (2*varianceFloor w hw0)) (intrinsicForm hw0 hw1 (state hw) (state hw)) := by
  have hfloor := centered_norm_floor hw0 hw1 width faces coefficient (faces_physical hw)
    faces_nodup
  have hbudget : varianceFloor w hw0 *
      SU2FiniteTrivalentPacketGraphFullSupportNorm.listQSum
        (fun p => coefficient p*coefficient p) faces ≈ 2*varianceFloor w hw0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ coefficient_square_budget)
      (Q'.mul_comm_eqv _ _)
  have hleft : Equiv (ofQ' (varianceFloor w hw0 *
      SU2FiniteTrivalentPacketGraphFullSupportNorm.listQSum
        (fun p => coefficient p*coefficient p) faces)) (ofQ' (2*varianceFloor w hw0)) :=
    SumOfSquares.Equiv_of_approx_eqv (fun _ => hbudget)
  have hright := centeredMoment_uncentered hw0 hw1 hw 0
  rw [advance_zero] at hright
  exact leEv_trans (leEv_of_equiv hleft.symm)
    (leEv_trans hfloor (leEv_of_equiv hright))

/-- Initial squared norm on the existing completed carrier. Fixed strict
nome only: this does not assert a scaling-uniform positive floor. -/
theorem excitation_norm_floor :
    RCle (Quotient.mk crealSetoid (ofQ' (2*varianceFloor w hw0)))
      (completedInner hw0 hw1 (excitation hw0 hw1 hw).val (excitation hw0 hw1 hw).val) := by
  change RCle _ (completedInner hw0 hw1 (embed hw0 hw1 (state hw))
    (embed hw0 hw1 (state hw)))
  rw [completedInner_embed]
  exact state_norm_floor hw0 hw1 hw

theorem excitation_norm_ne_zero :
    completedInner hw0 hw1 (excitation hw0 hw1 hw).val (excitation hw0 hw1 hw).val ≠ RCzero := by
  intro hz
  have h := excitation_norm_floor hw0 hw1 hw
  rw [hz] at h
  have hle : 2*varianceFloor w hw0 ≤ (0 : Q') := by
    apply Q'.le_of_forall_pos_add
    intro epsilon he
    obtain ⟨N, hN⟩ := h epsilon he
    exact hN N (Nat.le_refl N)
  exact (by decide : ¬ (0 : Q') < (0 : Q'))
    (Q'.pos_of_lt_of_le
      (Q'.mul_pos (by decide : (0 : Q') < 2) (varianceFloor_positive hw0 hw1)) hle)

theorem excitation_ne_zero :
    (excitation hw0 hw1 hw).val ≠ embed hw0 hw1 (zero width) := by
  intro hz
  apply excitation_norm_ne_zero hw0 hw1 hw
  rw [hz, completedInner_embed]
  exact Quotient.sound (intrinsicForm_zero_left hw0 hw1 (zero width))

/-- Exact correlations under the existing completed time operator, not a
positive-time survival claim. -/
theorem excitation_correlator_pin (n : Nat) :
    completedInner hw0 hw1 (excitation hw0 hw1 hw).val
      (completedTime hw0 hw1 n (excitation hw0 hw1 hw).val) =
      Quotient.mk crealSetoid (centeredTimeMoment hw0 hw1 n (state hw) (state hw)) := by
  change completedInner hw0 hw1 (embed hw0 hw1 (state hw))
    (completedTime hw0 hw1 n (embed hw0 hw1 (state hw))) = _
  rw [completedTime_embed, completedInner_embed]
  exact Quotient.sound (centeredMoment_uncentered hw0 hw1 hw n).symm

/-- The actual nonzero two-face source is odd under the original spatial
swap. This is a produced source pin, not an assumed symmetry of MAIN. -/
theorem excitation_swap_odd :
    completedSwap hw0 hw1 (excitation hw0 hw1 hw).val =
      completedNeg hw0 hw1 (excitation hw0 hw1 hw).val := by
  let a : IntrinsicExpression width :=
    ⟨0, .loop 0 (plaquetteLoop face01
      (faces_physical hw face01 (by simp [faces]))) 1, Nat.le_refl 0⟩
  let b : IntrinsicExpression width :=
    ⟨0, .loop 0 (plaquetteLoop face02
      (faces_physical hw face02 (by simp [faces]))) 1, Nat.le_refl 0⟩
  have ha : swapIntrinsic a = b := by
    change (⟨0, .loop 0 (swapSourceLoop (plaquetteLoop face01
      (faces_physical hw face01 (by simp [faces])))) 1, _⟩ : IntrinsicExpression width) = b
    rw [swapSourceLoop_face01 hw]
  have hb : swapIntrinsic b = a := by
    change (⟨0, .loop 0 (swapSourceLoop (plaquetteLoop face02
      (faces_physical hw face02 (by simp [faces])))) 1, _⟩ : IntrinsicExpression width) = a
    rw [swapSourceLoop_face02 hw]
  have hstate : state hw = sum (smul 1 a)
      (sum (smul (-1) b) (smul 0 (unit width))) := by rfl
  have hsource : embed hw0 hw1 (state hw) =
      completedSub hw0 hw1 (embed hw0 hw1 a) (embed hw0 hw1 b) := by
    rw [hstate, ← completedAdd_embed, ← completedAdd_embed,
      ← completedSmul_embed, ← completedSmul_embed, ← completedSmul_embed,
      completedSmul_one, completedSmul_zero, completedAdd_zero]
    rfl
  change completedSwap hw0 hw1 (embed hw0 hw1 (state hw)) =
    completedNeg hw0 hw1 (embed hw0 hw1 (state hw))
  rw [hsource, completedSwap_sub, completedSwap_embed, completedSwap_embed, ha, hb]
  unfold completedSub completedNeg
  rw [completedSmul_add, completedSmul_mul,
    completedSmul_congr hw0 hw1 (by decide : (-1 : Q') * (-1) ≈ 1)
      (embed hw0 hw1 b), completedSmul_one]
  exact completedAdd_comm hw0 hw1 _ _

/-- Original time evolution retains the produced odd sector. No lower
bound on its positive-time norm is asserted. -/
theorem excitation_time_swap_odd (n : Nat) :
    completedSwap hw0 hw1 (completedTime hw0 hw1 n (excitation hw0 hw1 hw).val) =
      completedNeg hw0 hw1 (completedTime hw0 hw1 n (excitation hw0 hw1 hw).val) := by
  rw [completedSwap_time, excitation_swap_odd]
  unfold completedNeg
  rw [completedTime_smul]

/-- Project only the detector, retaining the actual evolved source and
its literal completed pairing. The dual norm contracts by `oddPart_norm_le`. -/
theorem excitation_time_oddPart_detector (n : Nat)
    (v : Completion hw0 hw1 width) :
    completedInner hw0 hw1 (completedTime hw0 hw1 n (excitation hw0 hw1 hw).val)
      (oddPart hw0 hw1 v) =
      completedInner hw0 hw1 (completedTime hw0 hw1 n (excitation hw0 hw1 hw).val) v :=
  oddPart_detector hw0 hw1 _ v (excitation_time_swap_odd hw0 hw1 hw n)

#print axioms state
#print axioms joint_mean_zero
#print axioms state_mean_zero
#print axioms state_mean_left_zero
#print axioms centeredMoment_uncentered
#print axioms excitation
#print axioms state_norm_floor
#print axioms excitation_norm_floor
#print axioms excitation_norm_ne_zero
#print axioms excitation_ne_zero
#print axioms excitation_correlator_pin
#print axioms excitation_swap_odd
#print axioms excitation_time_swap_odd
#print axioms excitation_time_oddPart_detector

end YMGap.Continuum.BF4WilsonAllNomeAntisymmetricPlaquette
