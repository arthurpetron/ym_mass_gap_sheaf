/-
# The completed BF4 sector transfer form is the pulled sector form

The completed canonical root-sector transfer is now concrete, but the
sector-local Poincare estimates are expressed as cutoff limits of pulled
finite matrix quadratics.  This file identifies those two quantities on the
dense sector-cylinder image.

For one fixed sector presentation, the structural inner regularity of
`<P_K f,f>` is independent of `K`: recoding the left finite-linear syntax
changes atom values but not its syntax tree.  Hence the literal same-cutoff
diagonal converges to the completed transfer pairing.  At every cutoff beyond
the presentation base, that diagonal is exactly the pulled sector matrix
quadratic.  Cofinal reindexing and constructive uniqueness of limits give the
claimed equality in `CReal.RC`.

This is the dense transfer-form half of the direct sector completion bridge.
It does not yet prove that moving head-centering is dense in the completed
sector vacuum complement, nor any carrier-independent strict rate,
thermodynamic limit, continuum QFT, or Clay mass-gap theorem.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovAdaptiveGraphNorm
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
import YMGap.Continuum.BF4PhysicalDenseStageDiagonalComparison

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseTransferForm

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
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
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderAdaptiveRecodingTailInhabited
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.BF4PhysicalCutoffStationarySourceTail
open YMGap.Continuum.BF4PhysicalDenseStageDiagonalComparison
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.FiniteDeterministicKernelPushforward

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One-sided Markov syntax preserves the inner rate -/

private theorem atomLinearInnerRegularity_markov_left_rate_eq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat)
    (left :
      YMGap.Continuum.BF4PhysicalCutoffStationaryBridge.CentralPhysicalUnitObservable)
    (right : CentralPhysicalLinearObservable)
    (epsilon : Q') :
    (atomLinearInnerLimitInnerRegularity hw0 hw1 half
      (centralPhysicalMarkovCutoffUnitObservable
        (Q'.le_of_lt hw0) cutoff half left)
      right).rate epsilon =
      (atomLinearInnerLimitInnerRegularity
        hw0 hw1 half left right).rate epsilon := by
  induction right generalizing epsilon with
  | zero => rfl
  | atom right => rfl
  | add first second hfirst hsecond =>
      simp only [atomLinearInnerLimitInnerRegularity,
        CReal.InnerRegularity.add]
      rw [hfirst, hsecond]
  | smul scalar right hinduction =>
      simp only [atomLinearInnerLimitInnerRegularity,
        CReal.InnerRegularity.scaleLeftSigned]
      rw [hinduction]

/-- Recoding only the left argument preserves the explicit structural inner
regularity rate.  The rate of an atomic pairing does not inspect the atom
value, and the claim follows by recursion on the left syntax tree. -/
theorem innerLimitInnerRegularity_markov_left_rate_eq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat)
    (left right : CentralPhysicalLinearObservable)
    (epsilon : Q') :
    (innerLimitInnerRegularity hw0 hw1 half
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) cutoff half left)
      right).rate epsilon =
      (innerLimitInnerRegularity hw0 hw1 half left right).rate epsilon := by
  induction left generalizing epsilon with
  | zero => rfl
  | atom left =>
      exact atomLinearInnerRegularity_markov_left_rate_eq
        hw0 hw1 half cutoff left right epsilon
  | add first second hfirst hsecond =>
      simp only [centralPhysicalLinearMarkovCutoffAction,
        innerLimitInnerRegularity, CReal.InnerRegularity.add]
      rw [hfirst, hsecond]
  | smul scalar left hinduction =>
      simp only [centralPhysicalLinearMarkovCutoffAction,
        innerLimitInnerRegularity, CReal.InnerRegularity.scaleLeftSigned]
      rw [hinduction]

/-- The same one-sided invariance after the regularity witness is
regularized for direct diagonal convergence. -/
theorem regularizedInnerRegularity_markov_left_rate_eq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat)
    (left right : CentralPhysicalLinearObservable)
    (epsilon : Q') :
    (regularizedInnerRegularity
      (innerLimitInnerRegularity hw0 hw1 half
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) cutoff half left)
        right)).rate epsilon =
      (regularizedInnerRegularity
        (innerLimitInnerRegularity hw0 hw1 half left right)).rate epsilon := by
  unfold regularizedInnerRegularity regularInnerRate
  apply congrArg (fun rate : Nat -> Nat => CReal.Gmax rate (CReal.lv epsilon))
  funext precision
  exact innerLimitInnerRegularity_markov_left_rate_eq
    hw0 hw1 half cutoff left right (Q'.invSucc precision)

/-! ## 2. The finite same-cutoff identity -/

/-- The same-cutoff pairing of a recoded observable with its input is the
finite physical joint quadratic.  Factoring this generic statement keeps the
larger sector presentation out of the elaboration of finite self-adjointness. -/
theorem innerLimit_markovCutoffAction_pair_approx_eqv_joint
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half later : Nat)
    (observable : CentralPhysicalLinearObservable) :
    (innerLimit hw0 hw1 half
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) later half observable)
      observable).approx later ≈
      centralPhysicalJointQuadratic
        w (Q'.le_of_lt hw0) later half observable.value := by
  have hstage := innerLimit_approx_eqv_stage hw0 hw1 half later
    (centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) later half observable)
    observable
  rw [centralPhysicalSmulGNS_B_eq] at hstage
  have hrecoded :
      centralPhysicalWeightedInner w (Q'.le_of_lt hw0) later half
          (centralPhysicalLinearMarkovCutoffAction
            (Q'.le_of_lt hw0) later half observable).value
          observable.value ≈
        centralPhysicalWeightedInner w (Q'.le_of_lt hw0) later half
          (centralPhysicalMarkovApply w (Q'.le_of_lt hw0) later half
            observable.value)
          observable.value := by
    unfold centralPhysicalWeightedInner
    apply listQSum_congr_on
    intro source hsource
    apply Q'.mul_eqv_congr_left
    exact Q'.mul_eqv_congr_right _ _ _
      (centralPhysicalLinearMarkovCutoffAction_value_of_mem
        (Q'.le_of_lt hw0) later half observable source hsource)
  refine Q'.eqv_trans _
    (centralPhysicalWeightedInner w (Q'.le_of_lt hw0) later half
      (centralPhysicalMarkovApply w (Q'.le_of_lt hw0) later half
        observable.value)
      observable.value) _ (Q'.eqv_trans _ _ _ hstage hrecoded) ?_
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (centralPhysicalMarkovApply_self_adjoint
        w (Q'.le_of_lt hw0) later half observable.value observable.value))
    (centralPhysicalWeightedMarkovQuadratic_eq_joint
      w (Q'.le_of_lt hw0) later half observable.value)

/-- At every cutoff containing a sector presentation, its recoded Markov
pairing with the original presentation is exactly the pulled sector matrix
quadratic. -/
theorem centralPhysicalVacuumSectorCylinder_markovPair_approx_eqv_pulledMatrix
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half later : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half)
    (hbase : presentation.base <= later) :
    (innerLimit hw0 hw1 half
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) later half presentation.toLinearObservable)
      presentation.toLinearObservable).approx later ≈
      centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
        w (Q'.le_of_lt hw0) presentation.base later half
        presentation.coefficient := by
  exact Q'.eqv_trans _ _ _
    (innerLimit_markovCutoffAction_pair_approx_eqv_joint
      hw0 hw1 half later presentation.toLinearObservable)
    (centralPhysicalFiniteVacuumSectorLinearObservable_matrix_eqv_pulled
      hbase presentation.coefficient)

/-! ## 3. Identification of the completed dense transfer form -/

private def denseTransferPairingCauchy
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half) :=
  centralPhysicalLinearMarkovCutoffCauchy
    ((centralPhysicalDenseMarkovCauchyData hw0 hw1 half).modulus
      presentation.toLinearObservable)

private def denseTransferPairingStageRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half)
    (epsilon : Q') : Nat :=
  (regularizedInnerRegularity
    (innerLimitInnerRegularity hw0 hw1 half
      presentation.toLinearObservable
      presentation.toLinearObservable)).rate epsilon

/-- The literal same-cutoff dense transfer pairing converges to the completed
pairing of the dense transfer with the original presentation. -/
theorem centralPhysicalVacuumSectorCylinder_denseTransferPairingDiagonal_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half) :
    CReal.ConvergesTo
      (fun stage => CReal.ofQ'
        ((innerLimit hw0 hw1 half
          (centralPhysicalLinearMarkovCutoffAction
            (Q'.le_of_lt hw0) stage half presentation.toLinearObservable)
          presentation.toLinearObservable).approx stage))
      (physicalCauchyPairingLimit hw0 hw1 half
        (denseTransferPairingCauchy hw0 hw1 half presentation)
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant presentation.toLinearObservable)) := by
  apply physicalCauchyPairingRegularizedDiagonal_converges
    hw0 hw1 half
    (denseTransferPairingCauchy hw0 hw1 half presentation)
    ((centralPhysicalCutoffLinearSquaredSeminorm
      hw0 hw1 half).constant presentation.toLinearObservable)
    (denseTransferPairingStageRate hw0 hw1 half presentation)
  intro epsilon hepsilon stage hstage
  change
    (regularizedInnerRegularity
      (innerLimitInnerRegularity hw0 hw1 half
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) stage half presentation.toLinearObservable)
        presentation.toLinearObservable)).rate epsilon <= stage
  rw [regularizedInnerRegularity_markov_left_rate_eq]
  exact hstage

/-- The completed global pairing of the dense transfer of one sector
presentation with that presentation is represented by its pulled sector
matrix cutoff limit. -/
theorem centralPhysicalVacuumSectorCylinder_denseTransferPairing_equiv_pulledMatrix
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half) :
    CReal.Equiv
      (physicalCauchyPairingLimit hw0 hw1 half
        (denseTransferPairingCauchy hw0 hw1 half presentation)
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant presentation.toLinearObservable))
      (centralPhysicalFinitePulledVacuumSectorMatrixQuadraticCutoffLimit
        hw0 hw1 presentation.base half presentation.coefficient) := by
  let index := fun stage => max presentation.base stage
  let pairingSequence := fun stage => CReal.ofQ'
    ((innerLimit hw0 hw1 half
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) (index stage) half
        presentation.toLinearObservable)
      presentation.toLinearObservable).approx (index stage))
  let matrix :=
    centralPhysicalFinitePulledVacuumSectorMatrixQuadraticCutoffLimit
      hw0 hw1 presentation.base half presentation.coefficient
  apply CReal.Equiv_of_limit_of_equal
    (aSeq := pairingSequence)
    (bSeq := fun stage => CReal.ofQ' (matrix.approx (index stage)))
  · intro stage
    exact CReal.ofQ'_equiv_of_eqv
      (centralPhysicalVacuumSectorCylinder_markovPair_approx_eqv_pulledMatrix
        hw0 hw1 half (index stage) presentation (Nat.le_max_left _ _))
  · exact convergesTo_cofinalReindex
      (centralPhysicalVacuumSectorCylinder_denseTransferPairingDiagonal_converges
        hw0 hw1 half presentation)
      index (fun threshold => threshold)
      (fun threshold stage hstage =>
        Nat.le_trans hstage (Nat.le_max_right _ _))
  · exact convergesTo_cofinalReindex
      (CReal.convergesTo_self matrix)
      index (fun threshold => threshold)
      (fun threshold stage hstage =>
        Nat.le_trans hstage (Nat.le_max_right _ _))

/-- On the dense sector-cylinder image, the actual completed sector transfer
form is exactly the pulled finite-sector matrix cutoff limit. -/
theorem centralPhysicalVacuumSectorCylinder_completedTransferForm_embedRep_eq_pulled
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half) :
    centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCompletedTransfer hw0 hw1 half
          ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).embedRep presentation))
        ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
          hw0 hw1 half).embedRep presentation) =
      Quotient.mk CReal.crealSetoid
        (centralPhysicalFinitePulledVacuumSectorMatrixQuadraticCutoffLimit
          hw0 hw1 presentation.base half presentation.coefficient) := by
  unfold centralPhysicalVacuumSectorCylinderCompletedInner
  unfold centralPhysicalVacuumSectorCylinderCompletedTransfer
  rw [(centralPhysicalVacuumSectorCylinderTransferLiftData
    hw0 hw1 half).intertwines]
  rw [centralPhysicalVacuumSectorCylinderCompletionToGlobal_embedRep]
  rw [centralPhysicalConcreteAdaptiveCompletedMarkovTransfer_embed]
  apply Quotient.sound
  exact
    centralPhysicalVacuumSectorCylinder_denseTransferPairing_equiv_pulledMatrix
      hw0 hw1 half presentation

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseTransferForm

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseTransferForm.innerLimitInnerRegularity_markov_left_rate_eq
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseTransferForm.centralPhysicalVacuumSectorCylinder_markovPair_approx_eqv_pulledMatrix
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseTransferForm.centralPhysicalVacuumSectorCylinder_denseTransferPairingDiagonal_converges
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseTransferForm.centralPhysicalVacuumSectorCylinder_denseTransferPairing_equiv_pulledMatrix
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseTransferForm.centralPhysicalVacuumSectorCylinder_completedTransferForm_embedRep_eq_pulled
