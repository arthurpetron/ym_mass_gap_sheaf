/-
# Outer raw transfer-matrix convergence for completed BF4 sector vectors

An arbitrary sector Cauchy representative need not pay the cutoff modulus of
the pulled matrix Bishop real attached to its current dense term.  This file
constructs a cofinal, base-controlled slow diagonal which pays both that
matrix modulus and the same-object physical inner modulus.  Feeding the
result through the existing adaptive Markov sampler produces a sector
presentation sequence whose same-cutoff matrix values converge to the actual
completed transfer form.

The exported Type-level matrix regularity then lifts convergence of the
rational same-cutoff diagonal to convergence of the moving pulled-matrix
Bishop reals themselves.  The target is identified with the actual sector
transfer pairing of the original quotient vector.

This is the raw matrix half of the arbitrary-vector cofinality bridge.  No
head-centered matrix, common strict rate, thermodynamic, continuum, or Clay
claim is made here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Constructive.TrigAddCReal
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseTransferForm

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRawMatrix

set_option maxRecDepth 100000
set_option maxHeartbeats 15000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerKernel
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovAdaptiveGraphNorm
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormAdaptiveReindex
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionSchedule
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletedTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveGraphSchedule
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderAdaptiveRecodingTailInhabited
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderBaseControlledCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseTransferForm
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffStationarySourceTail
open YMGap.Continuum.BF4PhysicalDenseStageSlowDiagonalComparison
open YMGap.Continuum.CRealSeminormCompletion

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A generic paid-inner-diagonal lifting lemma -/

/-- If the rational self-index approximation of each moving constructive
real converges, and every sufficiently late outer stage pays an explicit
inner regularity of that real, then the constructive reals themselves
converge to the same limit. -/
theorem CReal.convergesTo_of_regularizedApproxDiagonal
    (sequence : Nat → CReal) (target : CReal)
    (regularity : ∀ stage, CReal.InnerRegularity (sequence stage))
    (stageRate : Q' → Nat)
    (rate_le_stage : ∀ epsilon : Q', (0 : Q') < epsilon →
      ∀ stage, stageRate epsilon ≤ stage →
        (regularity stage).rate epsilon ≤ stage)
    (diagonal_converges : CReal.ConvergesTo
      (fun stage => CReal.ofQ' ((sequence stage).approx stage)) target) :
    CReal.ConvergesTo sequence target := by
  intro epsilon hepsilon
  let q := HalfPow.half * epsilon
  have hq : (0 : Q') < q := ExpNeg.half_mul_pos epsilon hepsilon
  obtain ⟨outerStage, houterStage⟩ := diagonal_converges q hq
  refine ⟨max outerStage (stageRate q), fun stage hstage => ?_⟩
  have houter : outerStage ≤ stage :=
    Nat.le_trans (Nat.le_max_left _ _) hstage
  have hrateStage : stageRate q ≤ stage :=
    Nat.le_trans (Nat.le_max_right _ _) hstage
  have hinnerRate : (regularity stage).rate q ≤ stage :=
    rate_le_stage q hq stage hrateStage
  obtain ⟨outerApprox, houterApprox⟩ := houterStage stage houter
  refine ⟨max outerApprox ((regularity stage).rate q), fun later hlater => ?_⟩
  have hlaterOuter : outerApprox ≤ later :=
    Nat.le_trans (Nat.le_max_left _ _) hlater
  have hlaterInner : (regularity stage).rate q ≤ later :=
    Nat.le_trans (Nat.le_max_right _ _) hlater
  obtain ⟨hdiagForward, hdiagBackward⟩ :=
    houterApprox later hlaterOuter
  obtain ⟨hinnerForward, hinnerBackward⟩ :=
    (regularity stage).regular q hq later stage hlaterInner hinnerRate
  have htwo : q + q ≈ epsilon := ExpNeg.two_halves epsilon
  constructor
  · have hchain := Q'.le_trans' _ _ _ hinnerForward
      (Q'.add_le_add_right _ _ q hdiagForward)
    exact Q'.le_trans' _ _ _ hchain
      (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _
          (Q'.add_assoc_eqv _ q q)
          (Q'.add_eqv_congr_left _ (q + q) epsilon htwo)))
  · have hchain := Q'.le_trans' _ _ _ hdiagBackward
      (Q'.add_le_add_right _ _ q hinnerBackward)
    exact Q'.le_trans' _ _ _ hchain
      (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _
          (Q'.add_assoc_eqv _ q q)
          (Q'.add_eqv_congr_left _ (q + q) epsilon htwo)))

/-! ## 2. The sector matrix-admissible slow diagonal -/

def centralPhysicalVacuumSectorOuterMatrixRequirement
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (index : Nat) : Nat :=
  let controlled := centralPhysicalVacuumSectorBaseControlledCauchy X
  let presentation := controlled.seq index
  max
    ((regularizedInnerRegularity
      (innerLimitInnerRegularity hw0 hw1 half
        presentation.toLinearObservable
        presentation.toLinearObservable)).rate (Q'.invSucc index))
    ((regularizedInnerRegularity
      (centralPhysicalFinitePulledVacuumSectorMatrixQuadraticInnerRegularity
        hw0 hw1 presentation.base half presentation.coefficient)).rate
          (Q'.invSucc index))

def centralPhysicalVacuumSectorOuterMatrixSampleRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (threshold : Nat) : Nat :=
  slowThreshold
    (centralPhysicalVacuumSectorOuterMatrixRequirement hw0 hw1 half X)
    threshold

def centralPhysicalVacuumSectorOuterMatrixSampleIndex
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage : Nat) : Nat :=
  slowIndex
    (centralPhysicalVacuumSectorOuterMatrixRequirement hw0 hw1 half X)
    stage

def centralPhysicalVacuumSectorOuterMatrixDiagonalRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') : Nat :=
  centralPhysicalVacuumSectorOuterMatrixSampleRate hw0 hw1 half X
    (CReal.lv epsilon)

theorem centralPhysicalVacuumSectorOuterMatrixSampleIndex_cofinal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (threshold stage : Nat)
    (hstage : centralPhysicalVacuumSectorOuterMatrixSampleRate
      hw0 hw1 half X threshold ≤ stage) :
    threshold ≤ centralPhysicalVacuumSectorOuterMatrixSampleIndex
      hw0 hw1 half X stage :=
  slowIndex_cofinal
    (centralPhysicalVacuumSectorOuterMatrixRequirement hw0 hw1 half X)
    threshold stage hstage

theorem centralPhysicalVacuumSectorOuterMatrixSampleIndex_le_stage
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage : Nat) :
    centralPhysicalVacuumSectorOuterMatrixSampleIndex
        hw0 hw1 half X stage ≤ stage := by
  exact greatestAdmissibleAux_le
    (centralPhysicalVacuumSectorOuterMatrixRequirement hw0 hw1 half X)
    stage stage

/-- Every sufficiently late selected presentation pays both its ordinary
self-pair approximation rate and its pulled-matrix cutoff rate. -/
theorem centralPhysicalVacuumSectorOuterMatrix_selected_rates_paid
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (stage : Nat)
    (hstage : centralPhysicalVacuumSectorOuterMatrixDiagonalRate
      hw0 hw1 half X epsilon ≤ stage) :
    let controlled := centralPhysicalVacuumSectorBaseControlledCauchy X
    let index := centralPhysicalVacuumSectorOuterMatrixSampleIndex
      hw0 hw1 half X stage
    let presentation := controlled.seq index
    (regularizedInnerRegularity
      (innerLimitInnerRegularity hw0 hw1 half
        presentation.toLinearObservable
        presentation.toLinearObservable)).rate epsilon ≤ stage ∧
    (regularizedInnerRegularity
      (centralPhysicalFinitePulledVacuumSectorMatrixQuadraticInnerRegularity
        hw0 hw1 presentation.base half presentation.coefficient)).rate
          epsilon ≤ stage := by
  let required :=
    centralPhysicalVacuumSectorOuterMatrixRequirement hw0 hw1 half X
  let controlled := centralPhysicalVacuumSectorBaseControlledCauchy X
  let index := centralPhysicalVacuumSectorOuterMatrixSampleIndex
    hw0 hw1 half X stage
  let presentation := controlled.seq index
  have hzeroRate :
      centralPhysicalVacuumSectorOuterMatrixSampleRate
          hw0 hw1 half X 0 ≤
        centralPhysicalVacuumSectorOuterMatrixSampleRate
          hw0 hw1 half X (CReal.lv epsilon) :=
    slowThreshold_mono required (Nat.zero_le _)
  have hrequired : required index ≤ stage := by
    exact required_slowIndex_le required stage
      (Nat.le_trans hzeroRate hstage)
  have hprecision : CReal.lv epsilon ≤ index :=
    centralPhysicalVacuumSectorOuterMatrixSampleIndex_cofinal
      hw0 hw1 half X (CReal.lv epsilon) stage hstage
  have hinv : Q'.invSucc index ≤ epsilon :=
    Q'.le_trans' _ _ _
      (ExpNeg.invSucc_le_of_le hprecision)
      (CReal.invSucc_lv_le hepsilon)
  have hself := regularInnerRate_antitone
    (innerLimitInnerRegularity hw0 hw1 half
      presentation.toLinearObservable presentation.toLinearObservable)
    (Q'.invSucc_pos index) hinv
  have hmatrix := regularInnerRate_antitone
    (centralPhysicalFinitePulledVacuumSectorMatrixQuadraticInnerRegularity
      hw0 hw1 presentation.base half presentation.coefficient)
    (Q'.invSucc_pos index) hinv
  exact
    ⟨Nat.le_trans hself
        (Nat.le_trans (Nat.le_max_left _ _) hrequired),
      Nat.le_trans hmatrix
        (Nat.le_trans (Nat.le_max_right _ _) hrequired)⟩

/-- Cofinally normalize a sector representative so every late term pays both
matrix and physical self-pair inner cutoffs. -/
def centralPhysicalVacuumSectorOuterMatrixNormalizedCauchy
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy where
  seq stage := (centralPhysicalVacuumSectorBaseControlledCauchy X).seq
    (centralPhysicalVacuumSectorOuterMatrixSampleIndex
      hw0 hw1 half X stage)
  modulus epsilon :=
    centralPhysicalVacuumSectorOuterMatrixSampleRate hw0 hw1 half X
      ((centralPhysicalVacuumSectorBaseControlledCauchy X).modulus epsilon)
  isCauchy := by
    intro epsilon hepsilon first second hfirst hsecond
    exact (centralPhysicalVacuumSectorBaseControlledCauchy X).isCauchy
      epsilon hepsilon _ _
      (centralPhysicalVacuumSectorOuterMatrixSampleIndex_cofinal
        hw0 hw1 half X _ first hfirst)
      (centralPhysicalVacuumSectorOuterMatrixSampleIndex_cofinal
        hw0 hw1 half X _ second hsecond)

def centralPhysicalVacuumSectorOuterMatrixNormalizedClose
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Close X
      (centralPhysicalVacuumSectorOuterMatrixNormalizedCauchy
        hw0 hw1 half X) := by
  let D := centralPhysicalVacuumSectorCylinderSquaredSeminorm hw0 hw1 half
  let controlled := centralPhysicalVacuumSectorBaseControlledCauchy X
  let normalized := centralPhysicalVacuumSectorOuterMatrixNormalizedCauchy
    hw0 hw1 half X
  apply D.closeTrans (centralPhysicalVacuumSectorBaseControlledClose X)
  exact {
    modulus := fun epsilon => max (controlled.modulus epsilon)
      (centralPhysicalVacuumSectorOuterMatrixSampleRate
        hw0 hw1 half X (controlled.modulus epsilon))
    close := by
      intro epsilon hepsilon stage hstage
      have hraw : controlled.modulus epsilon ≤ stage :=
        Nat.le_trans (Nat.le_max_left _ _) hstage
      have hsampleRate :
          centralPhysicalVacuumSectorOuterMatrixSampleRate
              hw0 hw1 half X (controlled.modulus epsilon) ≤ stage :=
        Nat.le_trans (Nat.le_max_right _ _) hstage
      exact controlled.isCauchy epsilon hepsilon stage
        (centralPhysicalVacuumSectorOuterMatrixSampleIndex
          hw0 hw1 half X stage)
        hraw
        (centralPhysicalVacuumSectorOuterMatrixSampleIndex_cofinal
          hw0 hw1 half X (controlled.modulus epsilon) stage hsampleRate)
  }

/-! ## 3. Adaptive input presentations and paid rates -/

def centralPhysicalVacuumSectorOuterMatrixInputIndex
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage : Nat) : Nat :=
  let normalized := centralPhysicalVacuumSectorOuterMatrixNormalizedCauchy
    hw0 hw1 half X
  let global := centralPhysicalVacuumSectorCylinderCauchyToGlobal normalized
  centralPhysicalAdaptiveMarkovSampleIndex hw0 hw1 half
    (centralPhysicalDenseMarkovCauchyData hw0 hw1 half) global stage

def centralPhysicalVacuumSectorOuterMatrixInputCauchy
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy := by
  let normalized := centralPhysicalVacuumSectorOuterMatrixNormalizedCauchy
    hw0 hw1 half X
  let global := centralPhysicalVacuumSectorCylinderCauchyToGlobal normalized
  exact {
    seq := fun stage => normalized.seq
      (centralPhysicalVacuumSectorOuterMatrixInputIndex
        hw0 hw1 half X stage)
    modulus := fun epsilon =>
      centralPhysicalAdaptiveMarkovSampleRate hw0 hw1 half
        (centralPhysicalDenseMarkovCauchyData hw0 hw1 half) global
        (normalized.modulus epsilon)
    isCauchy := by
      intro epsilon hepsilon first second hfirst hsecond
      exact normalized.isCauchy epsilon hepsilon _ _
        (centralPhysicalAdaptiveMarkovSampleIndex_cofinal
          hw0 hw1 half
          (centralPhysicalDenseMarkovCauchyData hw0 hw1 half) global
          (normalized.modulus epsilon) first hfirst)
        (centralPhysicalAdaptiveMarkovSampleIndex_cofinal
          hw0 hw1 half
          (centralPhysicalDenseMarkovCauchyData hw0 hw1 half) global
          (normalized.modulus epsilon) second hsecond)
  }

def centralPhysicalVacuumSectorOuterMatrixInputClose
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Close X
      (centralPhysicalVacuumSectorOuterMatrixInputCauchy
        hw0 hw1 half X) := by
  let D := centralPhysicalVacuumSectorCylinderSquaredSeminorm hw0 hw1 half
  let normalized := centralPhysicalVacuumSectorOuterMatrixNormalizedCauchy
    hw0 hw1 half X
  let global := centralPhysicalVacuumSectorCylinderCauchyToGlobal normalized
  apply D.closeTrans
    (centralPhysicalVacuumSectorOuterMatrixNormalizedClose hw0 hw1 half X)
  exact {
    modulus := fun epsilon => max (normalized.modulus epsilon)
      (centralPhysicalAdaptiveMarkovSampleRate hw0 hw1 half
        (centralPhysicalDenseMarkovCauchyData hw0 hw1 half) global
        (normalized.modulus epsilon))
    close := by
      intro epsilon hepsilon stage hstage
      have hraw : normalized.modulus epsilon ≤ stage :=
        Nat.le_trans (Nat.le_max_left _ _) hstage
      have hsampleRate :
          centralPhysicalAdaptiveMarkovSampleRate hw0 hw1 half
              (centralPhysicalDenseMarkovCauchyData hw0 hw1 half) global
              (normalized.modulus epsilon) ≤ stage :=
        Nat.le_trans (Nat.le_max_right _ _) hstage
      exact normalized.isCauchy epsilon hepsilon stage
        (centralPhysicalVacuumSectorOuterMatrixInputIndex
          hw0 hw1 half X stage)
        hraw
        (centralPhysicalAdaptiveMarkovSampleIndex_cofinal
          hw0 hw1 half
          (centralPhysicalDenseMarkovCauchyData hw0 hw1 half) global
          (normalized.modulus epsilon) stage hsampleRate)
  }

theorem centralPhysicalVacuumSectorOuterMatrixInput_class_eq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    Quotient.mk
        (centralPhysicalVacuumSectorCylinderSquaredSeminorm
          hw0 hw1 half).completionSetoid X =
      Quotient.mk
        (centralPhysicalVacuumSectorCylinderSquaredSeminorm
          hw0 hw1 half).completionSetoid
        (centralPhysicalVacuumSectorOuterMatrixInputCauchy
          hw0 hw1 half X) :=
  Quotient.sound
    ⟨centralPhysicalVacuumSectorOuterMatrixInputClose hw0 hw1 half X⟩

theorem centralPhysicalVacuumSectorOuterMatrixInput_base_le_stage
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage : Nat) :
    ((centralPhysicalVacuumSectorOuterMatrixInputCauchy
      hw0 hw1 half X).seq stage).base ≤ stage := by
  let selected := centralPhysicalVacuumSectorOuterMatrixInputIndex
    hw0 hw1 half X stage
  let matrixIndex := centralPhysicalVacuumSectorOuterMatrixSampleIndex
    hw0 hw1 half X selected
  have hbase := centralPhysicalVacuumSectorBaseControlled_base_le_stage
    X matrixIndex
  have hmatrixSelected : matrixIndex ≤ selected :=
    centralPhysicalVacuumSectorOuterMatrixSampleIndex_le_stage
      hw0 hw1 half X selected
  have hselectedStage : selected ≤ stage :=
    centralPhysicalAdaptiveMarkovSampleIndex_le_stage
      hw0 hw1 half
      (centralPhysicalDenseMarkovCauchyData hw0 hw1 half)
      (centralPhysicalVacuumSectorCylinderCauchyToGlobal
        (centralPhysicalVacuumSectorOuterMatrixNormalizedCauchy
          hw0 hw1 half X)) stage
  exact Nat.le_trans hbase
    (Nat.le_trans hmatrixSelected hselectedStage)

def centralPhysicalVacuumSectorOuterMatrixAdaptiveDiagonalRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') : Nat :=
  let normalized := centralPhysicalVacuumSectorOuterMatrixNormalizedCauchy
    hw0 hw1 half X
  let global := centralPhysicalVacuumSectorCylinderCauchyToGlobal normalized
  centralPhysicalAdaptiveMarkovSampleRate hw0 hw1 half
    (centralPhysicalDenseMarkovCauchyData hw0 hw1 half) global
    (centralPhysicalVacuumSectorOuterMatrixDiagonalRate
      hw0 hw1 half X epsilon)

theorem centralPhysicalVacuumSectorOuterMatrixInput_rates_paid
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon)
    (stage : Nat)
    (hstage : centralPhysicalVacuumSectorOuterMatrixAdaptiveDiagonalRate
      hw0 hw1 half X epsilon ≤ stage) :
    let presentation :=
      (centralPhysicalVacuumSectorOuterMatrixInputCauchy
        hw0 hw1 half X).seq stage
    (regularizedInnerRegularity
      (innerLimitInnerRegularity hw0 hw1 half
        presentation.toLinearObservable
        presentation.toLinearObservable)).rate epsilon ≤ stage ∧
    (regularizedInnerRegularity
      (centralPhysicalFinitePulledVacuumSectorMatrixQuadraticInnerRegularity
        hw0 hw1 presentation.base half presentation.coefficient)).rate
          epsilon ≤ stage := by
  let normalized := centralPhysicalVacuumSectorOuterMatrixNormalizedCauchy
    hw0 hw1 half X
  let global := centralPhysicalVacuumSectorCylinderCauchyToGlobal normalized
  let selected := centralPhysicalVacuumSectorOuterMatrixInputIndex
    hw0 hw1 half X stage
  have hselected :
      centralPhysicalVacuumSectorOuterMatrixDiagonalRate
          hw0 hw1 half X epsilon ≤ selected :=
    centralPhysicalAdaptiveMarkovSampleIndex_cofinal
      hw0 hw1 half
      (centralPhysicalDenseMarkovCauchyData hw0 hw1 half) global
      (centralPhysicalVacuumSectorOuterMatrixDiagonalRate
        hw0 hw1 half X epsilon) stage hstage
  have hpaid :=
    centralPhysicalVacuumSectorOuterMatrix_selected_rates_paid
      hw0 hw1 half X epsilon hepsilon selected hselected
  have hselectedStage : selected ≤ stage :=
    centralPhysicalAdaptiveMarkovSampleIndex_le_stage
      hw0 hw1 half
      (centralPhysicalDenseMarkovCauchyData hw0 hw1 half) global stage
  exact ⟨Nat.le_trans hpaid.1 hselectedStage,
    Nat.le_trans hpaid.2 hselectedStage⟩

/-! ## 4. Raw pulled-matrix convergence and endpoint identification -/

def centralPhysicalVacuumSectorCylinderOuterPulledMatrixSeq
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) (stage : Nat) : CReal :=
  let presentation :=
    (centralPhysicalVacuumSectorOuterMatrixInputCauchy
      hw0 hw1 half X).seq stage
  centralPhysicalFinitePulledVacuumSectorMatrixQuadraticCutoffLimit
    hw0 hw1 presentation.base half presentation.coefficient

def centralPhysicalVacuumSectorOuterMatrixGlobalInputCauchy
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) :=
  centralPhysicalVacuumSectorCylinderCauchyToGlobal
    (centralPhysicalVacuumSectorOuterMatrixInputCauchy
      hw0 hw1 half X)

def centralPhysicalVacuumSectorOuterMatrixGlobalOutputCauchy
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) :=
  let normalized := centralPhysicalVacuumSectorOuterMatrixNormalizedCauchy
    hw0 hw1 half X
  let global := centralPhysicalVacuumSectorCylinderCauchyToGlobal normalized
  centralPhysicalAdaptiveMarkovMapCauchy
    (centralPhysicalDenseMarkovCauchyData hw0 hw1 half) global

def centralPhysicalVacuumSectorOuterMatrixPairingLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) : CReal :=
  physicalCauchyPairingLimit hw0 hw1 half
    (centralPhysicalVacuumSectorOuterMatrixGlobalOutputCauchy
      hw0 hw1 half X)
    (centralPhysicalVacuumSectorOuterMatrixGlobalInputCauchy
      hw0 hw1 half X)

def centralPhysicalVacuumSectorOuterMatrixActionInputDiagonalSeq
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) (stage : Nat) : CReal :=
  CReal.ofQ'
    ((innerLimit hw0 hw1 half
      ((centralPhysicalVacuumSectorOuterMatrixGlobalOutputCauchy
        hw0 hw1 half X).seq stage)
      ((centralPhysicalVacuumSectorOuterMatrixGlobalInputCauchy
        hw0 hw1 half X).seq stage)).approx stage)

def centralPhysicalVacuumSectorOuterMatrixApproxDiagonalSeq
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) (stage : Nat) : CReal :=
  CReal.ofQ'
    ((centralPhysicalVacuumSectorCylinderOuterPulledMatrixSeq X stage).approx
      stage)

theorem centralPhysicalVacuumSectorOuterMatrixActionInputDiagonal_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    CReal.ConvergesTo
      (centralPhysicalVacuumSectorOuterMatrixActionInputDiagonalSeq
        hw0 hw1 half X)
      (centralPhysicalVacuumSectorOuterMatrixPairingLimit
        hw0 hw1 half X) := by
  apply physicalCauchyPairingRegularizedDiagonal_converges
    hw0 hw1 half
    (centralPhysicalVacuumSectorOuterMatrixGlobalOutputCauchy
      hw0 hw1 half X)
    (centralPhysicalVacuumSectorOuterMatrixGlobalInputCauchy
      hw0 hw1 half X)
    (centralPhysicalVacuumSectorOuterMatrixAdaptiveDiagonalRate
      hw0 hw1 half X)
  intro epsilon hepsilon stage hstage
  change
    (regularizedInnerRegularity
      (innerLimitInnerRegularity hw0 hw1 half
        (centralPhysicalLinearMarkovCutoffAction
          (Q'.le_of_lt hw0) stage half
          ((centralPhysicalVacuumSectorOuterMatrixInputCauchy
            hw0 hw1 half X).seq stage).toLinearObservable)
        ((centralPhysicalVacuumSectorOuterMatrixInputCauchy
          hw0 hw1 half X).seq stage).toLinearObservable)).rate epsilon ≤ stage
  rw [regularizedInnerRegularity_markov_left_rate_eq]
  exact (centralPhysicalVacuumSectorOuterMatrixInput_rates_paid
    hw0 hw1 half X epsilon hepsilon stage hstage).1

/-- At one outer stage, the adaptive action-input diagonal is exactly the
same-cutoff approximation of that stage's pulled sector matrix real. -/
theorem centralPhysicalVacuumSectorOuterMatrix_actionInput_approx_eqv_matrix
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage : Nat) :
    (innerLimit hw0 hw1 half
      ((centralPhysicalVacuumSectorOuterMatrixGlobalOutputCauchy
        hw0 hw1 half X).seq stage)
      ((centralPhysicalVacuumSectorOuterMatrixGlobalInputCauchy
        hw0 hw1 half X).seq stage)).approx stage ≈
      (centralPhysicalVacuumSectorCylinderOuterPulledMatrixSeq X stage).approx
        stage := by
  let presentation :=
    (centralPhysicalVacuumSectorOuterMatrixInputCauchy
      hw0 hw1 half X).seq stage
  change
    (innerLimit hw0 hw1 half
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) stage half presentation.toLinearObservable)
      presentation.toLinearObservable).approx stage ≈
      centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
        w (Q'.le_of_lt hw0) presentation.base stage half
        presentation.coefficient
  exact centralPhysicalVacuumSectorCylinder_markovPair_approx_eqv_pulledMatrix
    hw0 hw1 half stage presentation
    (centralPhysicalVacuumSectorOuterMatrixInput_base_le_stage
      hw0 hw1 half X stage)

theorem centralPhysicalVacuumSectorOuterMatrixApproxDiagonal_equiv_actionInput
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (stage : Nat) :
    CReal.Equiv
      (centralPhysicalVacuumSectorOuterMatrixApproxDiagonalSeq X stage)
      (centralPhysicalVacuumSectorOuterMatrixActionInputDiagonalSeq
        hw0 hw1 half X stage) := by
  exact CReal.ofQ'_equiv_of_eqv
    (Q'.eqv_symm
      (centralPhysicalVacuumSectorOuterMatrix_actionInput_approx_eqv_matrix
        hw0 hw1 half X stage))

theorem centralPhysicalVacuumSectorOuterMatrixApproxDiagonal_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    CReal.ConvergesTo
      (centralPhysicalVacuumSectorOuterMatrixApproxDiagonalSeq X)
      (centralPhysicalVacuumSectorOuterMatrixPairingLimit
        hw0 hw1 half X) := by
  intro epsilon hepsilon
  let q := HalfPow.half * epsilon
  have hq : (0 : Q') < q := ExpNeg.half_mul_pos epsilon hepsilon
  obtain ⟨outerStage, houterStage⟩ :=
    centralPhysicalVacuumSectorOuterMatrixActionInputDiagonal_converges
      hw0 hw1 half X q hq
  refine ⟨outerStage, fun stage hstage => ?_⟩
  obtain ⟨actionApprox, hactionApprox⟩ := houterStage stage hstage
  obtain ⟨equivApprox, hequivApprox⟩ :=
    (centralPhysicalVacuumSectorOuterMatrixApproxDiagonal_equiv_actionInput
      hw0 hw1 half X stage) q hq
  refine ⟨max actionApprox equivApprox, fun later hlater => ?_⟩
  have hlaterAction : actionApprox ≤ later :=
    Nat.le_trans (Nat.le_max_left _ _) hlater
  have hlaterEquiv : equivApprox ≤ later :=
    Nat.le_trans (Nat.le_max_right _ _) hlater
  obtain ⟨hactionForward, hactionBackward⟩ :=
    hactionApprox later hlaterAction
  obtain ⟨hequivForward, hequivBackward⟩ :=
    hequivApprox later hlaterEquiv
  have htwo : q + q ≈ epsilon := ExpNeg.two_halves epsilon
  constructor
  · have hchain := Q'.le_trans' _ _ _ hequivForward
      (Q'.add_le_add_right _ _ q hactionForward)
    exact Q'.le_trans' _ _ _ hchain
      (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _
          (Q'.add_assoc_eqv _ q q)
          (Q'.add_eqv_congr_left _ (q + q) epsilon htwo)))
  · have hchain := Q'.le_trans' _ _ _ hactionBackward
      (Q'.add_le_add_right _ _ q hequivBackward)
    exact Q'.le_trans' _ _ _ hchain
      (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _
          (Q'.add_assoc_eqv _ q q)
          (Q'.add_eqv_congr_left _ (q + q) epsilon htwo)))

/-- The moving pulled raw matrix Bishop reals of the constructed cofinal
presentation converge to the actual completed transfer-form representative. -/
theorem centralPhysicalVacuumSectorCylinder_outerPulledMatrix_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    CReal.ConvergesTo
      (centralPhysicalVacuumSectorCylinderOuterPulledMatrixSeq X)
      (centralPhysicalVacuumSectorOuterMatrixPairingLimit
        hw0 hw1 half X) := by
  apply CReal.convergesTo_of_regularizedApproxDiagonal
    (centralPhysicalVacuumSectorCylinderOuterPulledMatrixSeq X)
    (centralPhysicalVacuumSectorOuterMatrixPairingLimit hw0 hw1 half X)
    (fun stage =>
      let presentation :=
        (centralPhysicalVacuumSectorOuterMatrixInputCauchy
          hw0 hw1 half X).seq stage
      regularizedInnerRegularity
        (centralPhysicalFinitePulledVacuumSectorMatrixQuadraticInnerRegularity
          hw0 hw1 presentation.base half presentation.coefficient))
    (centralPhysicalVacuumSectorOuterMatrixAdaptiveDiagonalRate
      hw0 hw1 half X)
  · intro epsilon hepsilon stage hstage
    exact (centralPhysicalVacuumSectorOuterMatrixInput_rates_paid
      hw0 hw1 half X epsilon hepsilon stage hstage).2
  · exact centralPhysicalVacuumSectorOuterMatrixApproxDiagonal_converges
      hw0 hw1 half X

/-- The raw-matrix convergence target represents the actual completed sector
transfer pairing of the original quotient vector. -/
theorem centralPhysicalVacuumSectorCylinder_completedTransferForm_mk_eq_outerRawMatrixLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCompletedTransfer hw0 hw1 half
          (Quotient.mk
            (centralPhysicalVacuumSectorCylinderSquaredSeminorm
              hw0 hw1 half).completionSetoid X))
        (Quotient.mk
          (centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).completionSetoid X) =
      Quotient.mk CReal.crealSetoid
        (centralPhysicalVacuumSectorOuterMatrixPairingLimit
          hw0 hw1 half X) := by
  let sectorD :=
    centralPhysicalVacuumSectorCylinderSquaredSeminorm hw0 hw1 half
  let globalD := centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half
  let input := centralPhysicalVacuumSectorOuterMatrixInputCauchy
    hw0 hw1 half X
  let normalized := centralPhysicalVacuumSectorOuterMatrixNormalizedCauchy
    hw0 hw1 half X
  let global := centralPhysicalVacuumSectorCylinderCauchyToGlobal normalized
  let globalInput := centralPhysicalVacuumSectorOuterMatrixGlobalInputCauchy
    hw0 hw1 half X
  let globalOutput := centralPhysicalVacuumSectorOuterMatrixGlobalOutputCauchy
    hw0 hw1 half X
  have hclass : Quotient.mk sectorD.completionSetoid X =
      Quotient.mk sectorD.completionSetoid input :=
    centralPhysicalVacuumSectorOuterMatrixInput_class_eq hw0 hw1 half X
  rw [hclass]
  unfold centralPhysicalVacuumSectorCylinderCompletedInner
    centralPhysicalVacuumSectorCylinderCompletedTransfer
  rw [(centralPhysicalVacuumSectorCylinderTransferLiftData
    hw0 hw1 half).intertwines]
  have hglobalInput :
      Quotient.mk globalD.completionSetoid global =
        Quotient.mk globalD.completionSetoid globalInput := by
    exact centralPhysicalAdaptiveMarkovInputMap_class_eq
      (centralPhysicalDenseMarkovCauchyData hw0 hw1 half) global
  have htransfer :
      centralPhysicalConcreteAdaptiveCompletedMarkovTransfer hw0 hw1 half
          (Quotient.mk globalD.completionSetoid globalInput) =
        Quotient.mk globalD.completionSetoid globalOutput := by
    rw [← hglobalInput]
    rfl
  change centralPhysicalCutoffCompletedInner hw0 hw1 half
      (centralPhysicalConcreteAdaptiveCompletedMarkovTransfer hw0 hw1 half
        (Quotient.mk globalD.completionSetoid globalInput))
      (Quotient.mk globalD.completionSetoid globalInput) = _
  rw [htransfer]
  rfl

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRawMatrix

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRawMatrix.CReal.convergesTo_of_regularizedApproxDiagonal
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRawMatrix.centralPhysicalVacuumSectorOuterMatrixInput_class_eq
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRawMatrix.centralPhysicalVacuumSectorCylinder_outerPulledMatrix_converges
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRawMatrix.centralPhysicalVacuumSectorCylinder_completedTransferForm_mk_eq_outerRawMatrixLimit
