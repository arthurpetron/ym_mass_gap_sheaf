/-
# Positive self-adjointness of the actual cutoff-removed conditional action

The existing adaptive construction supplies an operator on the completed
marginal-norm carrier. Here its form is proved self-adjoint and between zero
and the marginal norm on EVERY completed vector. A shared adaptive diagonal
keeps both insertions at the same finite physical cutoff. Right-action rate
invariance follows from the already proved left- and both-action invariance;
no new Cauchy certificate or stronger sampler is assumed.

These laws make E(x,y)=B(x,Py) a genuine positive reflected candidate form on
this carrier. The constructive-real cubic identity proves that the SAME P
is positive, self-adjoint and contractive for E, with the SAME unit vacuum,
vacuum pairing and exact one-insertion-shifted moments. E may have a radical;
no equivalence to B or completeness for E is claimed. Identifying the E
completion's root-sector part with the all-spin raw cube completion,
geometric time and a strict gap remain open. The full marginal carrier can
have other sectors; no whole-carrier identification with the cube sector is
asserted.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveCauchySchwarz
import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveNonexpansive
import YMGap.Continuum.RCPositiveContractionOneStep
import YMGap.Continuum.PositiveContractionOneStepCompletion

namespace YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerLaws
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerKernel
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedAlgebra
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovAdaptiveGraphNorm
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormAdaptiveReindex
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormRateInvariance
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletedTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveSchedule
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveCauchySchwarz
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.BF4PhysicalCutoffStationarySourceTail
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseTransferForm
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseMarkovFormCauchySchwarz
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalMarkovTransferLaws
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.CRealSeminormCompletion

local infix:50 " ≈ " => Q'.eqv

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (half : Nat)

theorem right_action_rate (K : Nat) (a b : CentralPhysicalLinearObservable) (epsilon : Q') :
    (regularizedInnerRegularity (innerLimitInnerRegularity hw0 hw1 half a
      (centralPhysicalLinearMarkovCutoffAction (Q'.le_of_lt hw0) K half b))).rate epsilon =
    (regularizedInnerRegularity (innerLimitInnerRegularity hw0 hw1 half a b)).rate epsilon := by
  unfold regularizedInnerRegularity regularInnerRate
  apply congrArg (fun rate : Nat → Nat => CReal.Gmax rate (CReal.lv epsilon))
  funext precision
  exact Eq.trans (innerLimitInnerRegularity_markov_left_rate_eq hw0 hw1 half K a
    (centralPhysicalLinearMarkovCutoffAction (Q'.le_of_lt hw0) K half b) _).symm
    (innerLimitInnerRegularity_markov_both_rate_eq hw0 hw1 half K a b _)

private theorem stage_symm (K : Nat) (a b : CentralPhysicalLinearObservable) :
    (innerLimit hw0 hw1 half a b).approx K ≈ (innerLimit hw0 hw1 half b a).approx K := by
  let D := (centralPhysicalSmulGNS w (Q'.le_of_lt hw0) K half).toGNSData
  exact Q'.eqv_trans _ _ _ (innerLimit_approx_eqv_stage hw0 hw1 half K a b)
    (Q'.eqv_trans _ _ _ (D.B_symm a.value b.value)
      (Q'.eqv_symm (innerLimit_approx_eqv_stage hw0 hw1 half K b a)))

private theorem stage_selfAdjoint (K : Nat) (a b : CentralPhysicalLinearObservable) :
    (innerLimit hw0 hw1 half (centralPhysicalLinearMarkovCutoffAction (Q'.le_of_lt hw0) K half a) b).approx K ≈
    (innerLimit hw0 hw1 half a (centralPhysicalLinearMarkovCutoffAction (Q'.le_of_lt hw0) K half b)).approx K := by
  let D := (centralPhysicalSmulGNS w (Q'.le_of_lt hw0) K half).toGNSData
  refine Q'.eqv_trans _ _ _ (innerLimit_markovCutoffAction_cross_approx_eqv_form hw0 hw1 half K a b) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm
    (centralPhysicalMarkovApply_self_adjoint w (Q'.le_of_lt hw0) K half a.value b.value)) ?_
  refine Q'.eqv_trans _ _ _ (D.B_symm a.value (centralPhysicalMarkovApply w (Q'.le_of_lt hw0) K half b.value)) ?_
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (innerLimit_markovCutoffAction_cross_approx_eqv_form hw0 hw1 half K b a))
    (Q'.eqv_symm (stage_symm hw0 hw1 half K a _))

variable (pointwise : CentralPhysicalLinearMarkovDenseCauchyData hw0 hw1 half)

local notation "D" => centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half
local notation "B" => centralPhysicalCutoffCompletedInner hw0 hw1 half
local notation "P" => centralPhysicalAdaptiveCompletedMarkovTransfer pointwise
local notation "LX" => centralPhysicalJointAdaptiveLeftInputCauchy hw0 hw1 half pointwise
local notation "LY" => centralPhysicalJointAdaptiveRightInputCauchy hw0 hw1 half pointwise
local notation "TX" => centralPhysicalJointAdaptiveLeftActionCauchy hw0 hw1 half pointwise
local notation "TY" => centralPhysicalJointAdaptiveRightActionCauchy hw0 hw1 half pointwise

/-- The missing right insertion uses exactly the existing shared sampler. -/
theorem jointRightCross_converges (X Y : (D).Cauchy) :
    CReal.ConvergesTo (fun K => CReal.ofQ'
      ((innerLimit hw0 hw1 half ((LX X Y).seq K) ((TY X Y).seq K)).approx K))
      (physicalCauchyPairingLimit hw0 hw1 half (LX X Y) (TY X Y)) := by
  apply physicalCauchyPairingRegularizedDiagonal_converges hw0 hw1 half (LX X Y) (TY X Y)
    (fun epsilon => centralPhysicalJointAdaptiveMarkovSampleRate hw0 hw1 half pointwise X Y (CReal.lv epsilon))
  intro epsilon hepsilon K hK
  change (regularizedInnerRegularity (innerLimitInnerRegularity hw0 hw1 half
    (X.seq (centralPhysicalJointAdaptiveMarkovSampleIndex hw0 hw1 half pointwise X Y K))
    (centralPhysicalLinearMarkovCutoffAction (Q'.le_of_lt hw0) K half
      (Y.seq (centralPhysicalJointAdaptiveMarkovSampleIndex hw0 hw1 half pointwise X Y K))))).rate epsilon ≤ K
  rw [right_action_rate]
  exact (centralPhysicalJointAdaptiveMarkov_inner_rates_paid hw0 hw1 half pointwise X Y epsilon hepsilon K hK).2.2

theorem joint_selfAdjoint (X Y : (D).Cauchy) :
    CReal.Equiv (physicalCauchyPairingLimit hw0 hw1 half (TX X Y) (LY X Y))
      (physicalCauchyPairingLimit hw0 hw1 half (LX X Y) (TY X Y)) := by
  apply CReal.Equiv_of_limit_of_equal _
    (centralPhysicalJointAdaptiveMarkovCrossForm_converges hw0 hw1 half pointwise X Y)
    (jointRightCross_converges hw0 hw1 half pointwise X Y)
  intro K
  exact CReal.ofQ'_equiv_of_eqv (stage_selfAdjoint hw0 hw1 half K _ _)

/-- Self-adjointness on the actual completed carrier, not on a surrogate. -/
theorem completed_selfAdjoint (x y : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    B (P x) y = B x (P y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  let l := centralPhysicalJointAdaptiveMarkovLeftSample hw0 hw1 half pointwise X Y
  let r := centralPhysicalJointAdaptiveMarkovRightSample hw0 hw1 half pointwise X Y
  have hLX := centralPhysicalAdmissibleMarkovInput_class_eq l
  have hLY := centralPhysicalAdmissibleMarkovInput_class_eq r
  have hTX := centralPhysicalAdmissibleMarkovMap_class_eq_adaptive hw0 hw1 half pointwise X l
  have hTY := centralPhysicalAdmissibleMarkovMap_class_eq_adaptive hw0 hw1 half pointwise Y r
  rw [centralPhysicalAdaptiveCompletedMarkovTransfer_mk, centralPhysicalAdaptiveCompletedMarkovTransfer_mk]
  rw [← hTX, ← hTY, hLX, hLY]
  exact Quotient.sound (joint_selfAdjoint hw0 hw1 half pointwise X Y)

private theorem jointInputSquare_converges (X Y : (D).Cauchy) :
    CReal.ConvergesTo (fun K => CReal.ofQ'
      ((innerLimit hw0 hw1 half ((LX X Y).seq K) ((LX X Y).seq K)).approx K))
      (physicalCauchyPairingLimit hw0 hw1 half (LX X Y) (LX X Y)) := by
  apply physicalCauchyPairingRegularizedDiagonal_converges hw0 hw1 half (LX X Y) (LX X Y)
    (fun epsilon => centralPhysicalJointAdaptiveMarkovSampleRate hw0 hw1 half pointwise X Y (CReal.lv epsilon))
  intro epsilon hepsilon K hK
  exact (centralPhysicalJointAdaptiveMarkov_inner_rates_paid hw0 hw1 half pointwise X Y epsilon hepsilon K hK).1

private theorem stage_form_interval (K : Nat) (a : CentralPhysicalLinearObservable) :
    (0 : Q') ≤ (innerLimit hw0 hw1 half
      (centralPhysicalLinearMarkovCutoffAction (Q'.le_of_lt hw0) K half a) a).approx K ∧
    (innerLimit hw0 hw1 half
      (centralPhysicalLinearMarkovCutoffAction (Q'.le_of_lt hw0) K half a) a).approx K ≤
      (innerLimit hw0 hw1 half a a).approx K := by
  let G := (centralPhysicalSmulGNS w (Q'.le_of_lt hw0) K half).toGNSData
  have he := Q'.eqv_trans _ _ _
    (innerLimit_markovCutoffAction_cross_approx_eqv_form hw0 hw1 half K a a)
    (G.B_symm (centralPhysicalMarkovApply w (Q'.le_of_lt hw0) K half a.value) a.value)
  have hf := centralPhysicalMarkovApply_form_interval w (Q'.le_of_lt hw0) K half a.value
  exact ⟨Q'.le_trans' _ _ _ hf.1 (Q'.ge_of_eqv he),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv he) (Q'.le_trans' _ _ _ hf.2
      (Q'.ge_of_eqv (innerLimit_approx_eqv_stage hw0 hw1 half K a a)))⟩

theorem joint_form_interval (X Y : (D).Cauchy) :
    CReal.leEv CReal.czero (physicalCauchyPairingLimit hw0 hw1 half (TX X Y) (LX X Y)) ∧
    CReal.leEv (physicalCauchyPairingLimit hw0 hw1 half (TX X Y) (LX X Y))
      (physicalCauchyPairingLimit hw0 hw1 half (LX X Y) (LX X Y)) := by
  have hT := centralPhysicalJointAdaptiveMarkovLeftSelfForm_converges hw0 hw1 half pointwise X Y
  constructor
  · apply CReal.leEv_of_convergesTo_le (CReal.convergesTo_self CReal.czero) hT
    intro K
    exact CReal.leEv_of_le (CReal.ofQ'_le_ofQ' (stage_form_interval hw0 hw1 half K _).1)
  · apply CReal.leEv_of_convergesTo_le hT (jointInputSquare_converges hw0 hw1 half pointwise X Y)
    intro K
    exact CReal.leEv_of_le (CReal.ofQ'_le_ofQ' (stage_form_interval hw0 hw1 half K _).2)

/-- Positivity and the form upper bound on EVERY completed vector. -/
theorem completed_form_interval (x : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    CReal.RCnonneg (B (P x) x) ∧ CReal.RCle (B (P x) x) (B x x) := by
  refine Quotient.inductionOn x ?_
  intro X
  let sample := centralPhysicalJointAdaptiveMarkovLeftSample hw0 hw1 half pointwise X X
  have hL := centralPhysicalAdmissibleMarkovInput_class_eq sample
  have hT := centralPhysicalAdmissibleMarkovMap_class_eq_adaptive hw0 hw1 half pointwise X sample
  rw [centralPhysicalAdaptiveCompletedMarkovTransfer_mk, ← hT, hL]
  exact joint_form_interval hw0 hw1 half pointwise X X

/-- No uninhabited Cauchy premise: specialize to the existing source-tail producer. -/
theorem concrete_selfAdjoint (x y : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    B (centralPhysicalConcreteAdaptiveCompletedMarkovTransfer hw0 hw1 half x) y =
      B x (centralPhysicalConcreteAdaptiveCompletedMarkovTransfer hw0 hw1 half y) :=
  completed_selfAdjoint hw0 hw1 half (centralPhysicalDenseMarkovCauchyData hw0 hw1 half) x y

theorem concrete_form_interval (x : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    CReal.RCnonneg (B (centralPhysicalConcreteAdaptiveCompletedMarkovTransfer hw0 hw1 half x) x) ∧
    CReal.RCle (B (centralPhysicalConcreteAdaptiveCompletedMarkovTransfer hw0 hw1 half x) x) (B x x) :=
  completed_form_interval hw0 hw1 half (centralPhysicalDenseMarkovCauchyData hw0 hw1 half) x

/-- The SAME actual cutoff-removed operator inserted into the marginal form. -/
def completedReflectedForm (x y : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) : CReal.RC :=
  B x (centralPhysicalConcreteAdaptiveCompletedMarkovTransfer hw0 hw1 half y)

theorem completedReflectedForm_symm (x y : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    completedReflectedForm hw0 hw1 half x y = completedReflectedForm hw0 hw1 half y x :=
  Eq.trans (concrete_selfAdjoint hw0 hw1 half x y).symm
    (centralPhysicalCutoffCompletedInner_symm hw0 hw1 half _ _)

theorem completedReflectedForm_add_left (x y z : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    completedReflectedForm hw0 hw1 half (completedPhysicalLinearAdd hw0 hw1 half x y) z =
      CReal.RCadd (completedReflectedForm hw0 hw1 half x z) (completedReflectedForm hw0 hw1 half y z) :=
  centralPhysicalCutoffCompletedInner_add_left hw0 hw1 half x y _

theorem completedReflectedForm_smul_left (s : Q') (x y : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    completedReflectedForm hw0 hw1 half (completedPhysicalLinearSmul hw0 hw1 half s x) y =
      CReal.RCscale s (completedReflectedForm hw0 hw1 half x y) :=
  centralPhysicalCutoffCompletedInner_smul_left hw0 hw1 half s x _

theorem completedReflectedForm_interval (x : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    CReal.RCnonneg (completedReflectedForm hw0 hw1 half x x) ∧
      CReal.RCle (completedReflectedForm hw0 hw1 half x x) (B x x) := by
  unfold completedReflectedForm
  rw [← concrete_selfAdjoint]
  exact concrete_form_interval hw0 hw1 half x

/-- The cubic identity now holds AFTER removal of the spin cutoff, for
every completed vector and the already-constructed physical conditional P. -/
theorem completedReflectedForm_contraction (x : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    CReal.RCle (completedReflectedForm hw0 hw1 half
      (centralPhysicalConcreteAdaptiveCompletedMarkovTransfer hw0 hw1 half x)
      (centralPhysicalConcreteAdaptiveCompletedMarkovTransfer hw0 hw1 half x))
      (completedReflectedForm hw0 hw1 half x x) := by
  apply RCPositiveContractionOneStep.oneStep_contraction
    (completedPhysicalLinearAdd hw0 hw1 half) (completedPhysicalLinearNeg hw0 hw1 half)
    B (centralPhysicalConcreteAdaptiveCompletedMarkovTransfer hw0 hw1 half)
    (centralPhysicalCutoffCompletedInner_add_left hw0 hw1 half)
  · intro a b
    exact Eq.trans (centralPhysicalCutoffCompletedInner_smul_left hw0 hw1 half (-1) a b)
      (RCPositiveContractionOneStep.scale_neg_one _)
  · exact centralPhysicalCutoffCompletedInner_symm hw0 hw1 half
  · exact fun a b => (concrete_selfAdjoint hw0 hw1 half a b).symm
  · exact fun a => (completedReflectedForm_interval hw0 hw1 half a).1
  · exact fun a => (completedReflectedForm_interval hw0 hw1 half a).2

/-- Vacuum pairing is unchanged, so this form uses the SAME notion of centering. -/
theorem completedReflectedForm_vacuum_pairing (x : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    completedReflectedForm hw0 hw1 half x (centralPhysicalCutoffCompletedVacuum hw0 hw1 half) =
      B x (centralPhysicalCutoffCompletedVacuum hw0 hw1 half) := by
  unfold completedReflectedForm
  rw [centralPhysicalConcreteAdaptiveCompletedMarkovTransfer_vacuum]

theorem completedReflectedForm_vacuum_norm_one :
    completedReflectedForm hw0 hw1 half (centralPhysicalCutoffCompletedVacuum hw0 hw1 half)
      (centralPhysicalCutoffCompletedVacuum hw0 hw1 half) = Quotient.mk CReal.crealSetoid CReal.cone :=
  Eq.trans (completedReflectedForm_vacuum_pairing hw0 hw1 half _)
    (centralPhysicalCutoffCompletedVacuum_inner_self_eq_one hw0 hw1 half)

theorem completedReflectedForm_transfer_selfAdjoint
    (x y : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    completedReflectedForm hw0 hw1 half (centralPhysicalConcreteAdaptiveCompletedMarkovTransfer hw0 hw1 half x) y =
      completedReflectedForm hw0 hw1 half x (centralPhysicalConcreteAdaptiveCompletedMarkovTransfer hw0 hw1 half y) :=
  concrete_selfAdjoint hw0 hw1 half x _

theorem completedReflectedForm_transfer_positive
    (x : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    CReal.RCnonneg (completedReflectedForm hw0 hw1 half
      (centralPhysicalConcreteAdaptiveCompletedMarkovTransfer hw0 hw1 half x) x) :=
  centralPhysicalCutoffCompletedInner_self_nonneg hw0 hw1 half _

/-- Same-operator macro moments; this does not assert a geometric time pin. -/
theorem completedReflectedForm_moments (n : Nat)
    (x y : CentralPhysicalCutoffLinearCompletion hw0 hw1 half) :
    completedReflectedForm hw0 hw1 half x
      (PositiveContractionOneStepCompletion.actionIterate
        (centralPhysicalConcreteAdaptiveCompletedMarkovTransfer hw0 hw1 half) n y) =
      B x (PositiveContractionOneStepCompletion.actionIterate
        (centralPhysicalConcreteAdaptiveCompletedMarkovTransfer hw0 hw1 half) (n + 1) y) := rfl

end YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws

#print axioms YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws.right_action_rate
#print axioms YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws.jointRightCross_converges
#print axioms YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws.joint_selfAdjoint
#print axioms YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws.completed_selfAdjoint
#print axioms YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws.joint_form_interval
#print axioms YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws.completed_form_interval
#print axioms YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws.concrete_selfAdjoint
#print axioms YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws.concrete_form_interval
#print axioms YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws.completedReflectedForm
#print axioms YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws.completedReflectedForm_symm
#print axioms YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws.completedReflectedForm_add_left
#print axioms YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws.completedReflectedForm_smul_left
#print axioms YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws.completedReflectedForm_interval
#print axioms YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws.completedReflectedForm_contraction
#print axioms YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws.completedReflectedForm_vacuum_pairing
#print axioms YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws.completedReflectedForm_vacuum_norm_one
#print axioms YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws.completedReflectedForm_transfer_selfAdjoint
#print axioms YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws.completedReflectedForm_transfer_positive
#print axioms YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws.completedReflectedForm_moments
