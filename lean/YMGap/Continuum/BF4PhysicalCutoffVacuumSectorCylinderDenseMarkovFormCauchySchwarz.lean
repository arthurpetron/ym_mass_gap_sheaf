/-
# Sharp Markov-form Cauchy--Schwarz on the dense BF4 root sector

At every finite cutoff the physical Markov form

  (left,right) |-> <P_K left,right>_K

is a positive rational GNS form, hence obeys sharp Cauchy--Schwarz.  For two
arbitrary finite-linear observables, the structural regularity of
`<P_K left,right>` is independent of `K`.  The same-cutoff rational form
therefore converges to the actual cutoff-removed completed pairing of the
dense transfer of `left` with `right`.

Passing the three finite Cauchy--Schwarz terms through those explicit limits
proves the sharp positive-Markov-form law on every pair of dense canonical
root-sector cylinders, even when their presentation bases differ.

This does not yet extend the law to arbitrary completed sector vectors, and
it supplies no common strict rate, thermodynamic limit, continuum QFT, or
Clay conclusion.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseTransferForm
import YMGap.Continuum.BF4PhysicalCompletedMarkovFormCauchySchwarz

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseMarkovFormCauchySchwarz

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCompletedMarkovFormCauchySchwarz
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerKernel
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovAdaptiveGraphNorm
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormAdaptiveReindex
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.BF4PhysicalCutoffStationarySourceTail
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderAdaptiveRecodingTailInhabited
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseTransferForm
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A cross same-cutoff Markov form -/

/-- The regular approximation of the dense cross pairing at the action
cutoff is exactly the corresponding finite positive Markov form. -/
theorem innerLimit_markovCutoffAction_cross_approx_eqv_form
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat)
    (left right : CentralPhysicalLinearObservable) :
    (innerLimit hw0 hw1 half
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) cutoff half left)
      right).approx cutoff ≈
      centralPhysicalWeightedInner w (Q'.le_of_lt hw0) cutoff half
        (centralPhysicalMarkovApply
          w (Q'.le_of_lt hw0) cutoff half left.value)
        right.value := by
  have hstage := innerLimit_approx_eqv_stage hw0 hw1 half cutoff
    (centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) cutoff half left)
    right
  rw [centralPhysicalSmulGNS_B_eq] at hstage
  have hrecoded :
      centralPhysicalWeightedInner w (Q'.le_of_lt hw0) cutoff half
          (centralPhysicalLinearMarkovCutoffAction
            (Q'.le_of_lt hw0) cutoff half left).value
          right.value ≈
        centralPhysicalWeightedInner w (Q'.le_of_lt hw0) cutoff half
          (centralPhysicalMarkovApply
            w (Q'.le_of_lt hw0) cutoff half left.value)
          right.value := by
    unfold centralPhysicalWeightedInner
    apply listQSum_congr_on
    intro source hsource
    apply Q'.mul_eqv_congr_left
    exact Q'.mul_eqv_congr_right _ _ _
      (centralPhysicalLinearMarkovCutoffAction_value_of_mem
        (Q'.le_of_lt hw0) cutoff half left source hsource)
  exact Q'.eqv_trans _ _ _ hstage hrecoded

private def denseMarkovCrossCauchy
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (left : CentralPhysicalLinearObservable) :=
  centralPhysicalLinearMarkovCutoffCauchy
    ((centralPhysicalDenseMarkovCauchyData hw0 hw1 half).modulus left)

private def denseMarkovCrossStageRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (left right : CentralPhysicalLinearObservable)
    (epsilon : Q') : Nat :=
  (regularizedInnerRegularity
    (innerLimitInnerRegularity hw0 hw1 half left right)).rate epsilon

/-- The cutoff-indexed finite Markov cross form converges to the literal
completed pairing of the dense cutoff-removed transfer with its test
observable. -/
theorem centralPhysicalDenseMarkovCrossForm_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (left right : CentralPhysicalLinearObservable) :
    CReal.ConvergesTo
      (fun cutoff => CReal.ofQ'
        (centralPhysicalWeightedInner w (Q'.le_of_lt hw0) cutoff half
          (centralPhysicalMarkovApply
            w (Q'.le_of_lt hw0) cutoff half left.value)
          right.value))
      (physicalCauchyPairingLimit hw0 hw1 half
        (denseMarkovCrossCauchy hw0 hw1 half left)
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant right)) := by
  have hdiagonal : CReal.ConvergesTo
      (fun cutoff => CReal.ofQ'
        ((innerLimit hw0 hw1 half
          (centralPhysicalLinearMarkovCutoffAction
            (Q'.le_of_lt hw0) cutoff half left)
          right).approx cutoff))
      (physicalCauchyPairingLimit hw0 hw1 half
        (denseMarkovCrossCauchy hw0 hw1 half left)
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant right)) := by
    apply physicalCauchyPairingRegularizedDiagonal_converges
      hw0 hw1 half
      (denseMarkovCrossCauchy hw0 hw1 half left)
      ((centralPhysicalCutoffLinearSquaredSeminorm
        hw0 hw1 half).constant right)
      (denseMarkovCrossStageRate hw0 hw1 half left right)
    intro epsilon hepsilon cutoff hcutoff
    change
      (regularizedInnerRegularity
        (innerLimitInnerRegularity hw0 hw1 half
          (centralPhysicalLinearMarkovCutoffAction
            (Q'.le_of_lt hw0) cutoff half left)
          right)).rate epsilon <= cutoff
    rw [regularizedInnerRegularity_markov_left_rate_eq]
    exact hcutoff
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (s := fun cutoff => CReal.ofQ'
      ((innerLimit hw0 hw1 half
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) cutoff half left)
        right).approx cutoff))
  · intro cutoff
    exact CReal.ofQ'_equiv_of_eqv
      (innerLimit_markovCutoffAction_cross_approx_eqv_form
        hw0 hw1 half cutoff left right)
  · exact hdiagonal

/-! ## 2. Pass finite Cauchy--Schwarz through the three limits -/

/-- Sharp Cauchy--Schwarz for the actual cutoff-removed Markov form on two
dense finite-linear observables. -/
theorem centralPhysicalDenseMarkovFormLimit_cauchy_schwarz
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (left right : CentralPhysicalLinearObservable) :
    CReal.leEv
      (CReal.mul
        (physicalCauchyPairingLimit hw0 hw1 half
          (denseMarkovCrossCauchy hw0 hw1 half left)
          ((centralPhysicalCutoffLinearSquaredSeminorm
            hw0 hw1 half).constant right))
        (physicalCauchyPairingLimit hw0 hw1 half
          (denseMarkovCrossCauchy hw0 hw1 half left)
          ((centralPhysicalCutoffLinearSquaredSeminorm
            hw0 hw1 half).constant right)))
      (CReal.mul
        (physicalCauchyPairingLimit hw0 hw1 half
          (denseMarkovCrossCauchy hw0 hw1 half left)
          ((centralPhysicalCutoffLinearSquaredSeminorm
            hw0 hw1 half).constant left))
        (physicalCauchyPairingLimit hw0 hw1 half
          (denseMarkovCrossCauchy hw0 hw1 half right)
          ((centralPhysicalCutoffLinearSquaredSeminorm
            hw0 hw1 half).constant right))) := by
  let form := fun cutoff
      (first second : CentralPhysicalLinearObservable) =>
    CReal.ofQ'
      (centralPhysicalWeightedInner w (Q'.le_of_lt hw0) cutoff half
        (centralPhysicalMarkovApply
          w (Q'.le_of_lt hw0) cutoff half first.value)
        second.value)
  apply CReal.leEv_of_convergesTo_le
    (CReal.convergesTo_mul_general
      (centralPhysicalDenseMarkovCrossForm_converges
        hw0 hw1 half left right)
      (centralPhysicalDenseMarkovCrossForm_converges
        hw0 hw1 half left right))
    (CReal.convergesTo_mul_general
      (centralPhysicalDenseMarkovCrossForm_converges
        hw0 hw1 half left left)
      (centralPhysicalDenseMarkovCrossForm_converges
        hw0 hw1 half right right))
  intro cutoff
  let A := centralPhysicalWeightedInner
    w (Q'.le_of_lt hw0) cutoff half
    (centralPhysicalMarkovApply
      w (Q'.le_of_lt hw0) cutoff half left.value)
    right.value
  let B := centralPhysicalWeightedInner
    w (Q'.le_of_lt hw0) cutoff half
    (centralPhysicalMarkovApply
      w (Q'.le_of_lt hw0) cutoff half left.value)
    left.value
  let C := centralPhysicalWeightedInner
    w (Q'.le_of_lt hw0) cutoff half
    (centralPhysicalMarkovApply
      w (Q'.le_of_lt hw0) cutoff half right.value)
    right.value
  have hfinite : A * A <= B * C :=
    centralPhysicalMarkovForm_cauchy_schwarz
      w (Q'.le_of_lt hw0) cutoff half left.value right.value
  have hlift : CReal.leEv
      (CReal.mul (CReal.ofQ' A) (CReal.ofQ' A))
      (CReal.mul (CReal.ofQ' B) (CReal.ofQ' C)) := by
    intro epsilon hepsilon
    exact ⟨0, fun approximation _ => Q'.le_trans' _ _ _ hfinite
      (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))⟩
  simpa only [form, A, B, C] using hlift

/-! ## 3. The actual completed dense sector statement -/

/-- The actual lifted sector transfer obeys positive-form Cauchy--Schwarz on
the dense canonical cylinder image.  No common-base recoding is needed. -/
theorem centralPhysicalVacuumSectorCylinderCompletedMarkovForm_embedRep_cauchy_schwarz
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (left right : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half) :
    CReal.RCle
      (CReal.RCmul
        (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
          (centralPhysicalVacuumSectorCylinderCompletedTransfer
            hw0 hw1 half
            ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
              hw0 hw1 half).embedRep left))
          ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).embedRep right))
        (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
          (centralPhysicalVacuumSectorCylinderCompletedTransfer
            hw0 hw1 half
            ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
              hw0 hw1 half).embedRep left))
          ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).embedRep right)))
      (CReal.RCmul
        (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
          (centralPhysicalVacuumSectorCylinderCompletedTransfer
            hw0 hw1 half
            ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
              hw0 hw1 half).embedRep left))
          ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).embedRep left))
        (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
          (centralPhysicalVacuumSectorCylinderCompletedTransfer
            hw0 hw1 half
            ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
              hw0 hw1 half).embedRep right))
          ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).embedRep right))) := by
  unfold centralPhysicalVacuumSectorCylinderCompletedInner
  unfold centralPhysicalVacuumSectorCylinderCompletedTransfer
  simp only [
    (centralPhysicalVacuumSectorCylinderTransferLiftData
      hw0 hw1 half).intertwines,
    centralPhysicalVacuumSectorCylinderCompletionToGlobal_embedRep,
    centralPhysicalConcreteAdaptiveCompletedMarkovTransfer_embed]
  change CReal.RCle
    (CReal.RCmul
      (Quotient.mk CReal.crealSetoid
        (physicalCauchyPairingLimit hw0 hw1 half
          (denseMarkovCrossCauchy hw0 hw1 half left.toLinearObservable)
          ((centralPhysicalCutoffLinearSquaredSeminorm
            hw0 hw1 half).constant right.toLinearObservable)))
      (Quotient.mk CReal.crealSetoid
        (physicalCauchyPairingLimit hw0 hw1 half
          (denseMarkovCrossCauchy hw0 hw1 half left.toLinearObservable)
          ((centralPhysicalCutoffLinearSquaredSeminorm
            hw0 hw1 half).constant right.toLinearObservable))))
    (CReal.RCmul
      (Quotient.mk CReal.crealSetoid
        (physicalCauchyPairingLimit hw0 hw1 half
          (denseMarkovCrossCauchy hw0 hw1 half left.toLinearObservable)
          ((centralPhysicalCutoffLinearSquaredSeminorm
            hw0 hw1 half).constant left.toLinearObservable)))
      (Quotient.mk CReal.crealSetoid
        (physicalCauchyPairingLimit hw0 hw1 half
          (denseMarkovCrossCauchy hw0 hw1 half right.toLinearObservable)
          ((centralPhysicalCutoffLinearSquaredSeminorm
            hw0 hw1 half).constant right.toLinearObservable))))
  rw [CReal.RCmul_mk, CReal.RCmul_mk, CReal.RCle_mk]
  exact centralPhysicalDenseMarkovFormLimit_cauchy_schwarz
    hw0 hw1 half left.toLinearObservable right.toLinearObservable

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseMarkovFormCauchySchwarz

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseMarkovFormCauchySchwarz.innerLimit_markovCutoffAction_cross_approx_eqv_form
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseMarkovFormCauchySchwarz.centralPhysicalDenseMarkovCrossForm_converges
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseMarkovFormCauchySchwarz.centralPhysicalDenseMarkovFormLimit_cauchy_schwarz
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseMarkovFormCauchySchwarz.centralPhysicalVacuumSectorCylinderCompletedMarkovForm_embedRep_cauchy_schwarz
