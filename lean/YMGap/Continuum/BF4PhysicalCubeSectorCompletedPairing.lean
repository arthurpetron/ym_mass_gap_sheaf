/-
# The comparison preserves the physical pairing on the completed sector

Slow the existing shared adaptive sampler just enough to pay literal cube
admission and the normalized form's inner regularity. Admissibility is
preserved, so the action representative still denotes the original physical
conditional transfer. The two aligned finite forms are eventually equal;
their limits identify the pairing on ALL completed marginal-sector vectors.

Scope: w=1/400, extent one, with the existing explicit Cauchy representatives.
Consequently the mapped sector action retains positivity, self-adjointness,
E-contraction and exact shifted macro moments. This is not yet a transfer
on the entire reflected completion, a stationary sector vacuum, a
geometric-time identification, or a strict spectral gap.
-/

import YMGap.Continuum.BF4PhysicalCubeSectorComparison
import YMGap.Continuum.BF4PhysicalAdmissibleSampleSlowdown

namespace YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalAdmissibleSampleSlowdown
open YMGap.Continuum.BF4PhysicalCubeGNSData
open YMGap.Continuum.BF4PhysicalCubeNormalizedKernelLimit
open YMGap.Continuum.BF4PhysicalCubeObservableRealization
open YMGap.Continuum.BF4PhysicalCubeReflectedCompletion
open YMGap.Continuum.BF4PhysicalCubeSectorComparison
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerKernel
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovAdaptiveGraphNorm
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormAdaptiveReindex
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovGraphNormRateInvariance
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletedTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveSchedule
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws
open YMGap.Continuum.BF4PhysicalCutoffStationarySourceTail
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderAdaptiveRecodingTailInhabited
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseMarkovFormCauchySchwarz
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseTransferForm
open YMGap.Continuum.BF4PhysicalDenseStageDiagonalComparison
open YMGap.Continuum.BF4PhysicalDenseStageSlowDiagonalComparison
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv
local notation "M" => centralPhysicalVacuumSectorCylinderSquaredSeminorm
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "G" => centralPhysicalCutoffLinearSquaredSeminorm
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "pointwise" => centralPhysicalDenseMarkovCauchyData
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "E" => completedReflectedForm (w := anchorCoupling) (by decide) (by decide) 0

variable (X Y : (M).Cauchy)

local notation "GX" => centralPhysicalVacuumSectorCylinderCauchyToGlobal X
local notation "GY" => centralPhysicalVacuumSectorCylinderCauchyToGlobal Y

def baseIndex : Nat → Nat :=
  centralPhysicalJointAdaptiveMarkovSampleIndex (by decide) (by decide) 0 pointwise GX GY

def baseRate : Nat → Nat :=
  centralPhysicalJointAdaptiveMarkovSampleRate (by decide) (by decide) 0 pointwise GX GY

def baseNormalized (n : Nat) : CReal :=
  normalizedFormLimit (w := anchorCoupling) (by decide) (by decide)
    (presentationToCube (X.seq (baseIndex X Y n))) (presentationToCube (Y.seq (baseIndex X Y n)))

def baseNormalizedRegularity (n : Nat) : CReal.InnerRegularity (baseNormalized X Y n) :=
  normalizedFormRegularity (w := anchorCoupling) (by decide) (by decide) _ _

/-- Both extra obligations concern the same pair chosen by the old sampler. -/
def extraRequirement (n : Nat) : Nat :=
  max (realizationCutoff (presentationToCube (X.seq (baseIndex X Y n)))
    (presentationToCube (Y.seq (baseIndex X Y n))))
    ((regularizedInnerRegularity (baseNormalizedRegularity X Y n)).rate (Q'.invSucc n))

def stageIndex (stage : Nat) : Nat := baseIndex X Y (slowIndex (extraRequirement X Y) stage)

def stageRate (threshold : Nat) : Nat := slowThreshold (extraRequirement X Y) (baseRate X Y threshold)

theorem stageIndex_cofinal (threshold stage : Nat) (hstage : stageRate X Y threshold ≤ stage) :
    threshold ≤ stageIndex X Y stage :=
  centralPhysicalJointAdaptiveMarkovSampleIndex_cofinal (by decide) (by decide) 0 pointwise GX GY
    threshold _ (slowIndex_cofinal (extraRequirement X Y) _ stage hstage)

def leftSample := slowSample
  (centralPhysicalJointAdaptiveMarkovLeftSample (by decide) (by decide) 0 pointwise GX GY)
  (extraRequirement X Y)

def rightSample := slowSample
  (centralPhysicalJointAdaptiveMarkovRightSample (by decide) (by decide) 0 pointwise GX GY)
  (extraRequirement X Y)

def leftAction : (G).Cauchy := centralPhysicalAdmissibleMarkovMapCauchy (leftSample X Y)
def rightInput : (G).Cauchy := centralPhysicalAdmissibleMarkovInputCauchy (rightSample X Y)

def physicalCrossLimit : CReal :=
  physicalCauchyPairingLimit (by decide) (by decide) 0 (leftAction X Y) (rightInput X Y)

def physicalCrossSequence (stage : Nat) : Q' :=
  (innerLimit (w := anchorCoupling) (by decide) (by decide) 0
    ((leftAction X Y).seq stage) ((rightInput X Y).seq stage)).approx stage

/-- No new transfer producer: this is the existing admissible action limit. -/
theorem physicalCross_converges :
    CReal.ConvergesTo (fun stage => CReal.ofQ' (physicalCrossSequence X Y stage))
      (physicalCrossLimit X Y) := by
  apply physicalCauchyPairingRegularizedDiagonal_converges (by decide) (by decide) 0
    (leftAction X Y) (rightInput X Y) (fun epsilon => stageRate X Y (CReal.lv epsilon))
  intro epsilon hepsilon stage hstage
  change (regularizedInnerRegularity (innerLimitInnerRegularity (w := anchorCoupling)
    (by decide) (by decide) 0
    (centralPhysicalLinearMarkovCutoffAction (by decide) stage 0 ((GX).seq (stageIndex X Y stage)))
    ((GY).seq (stageIndex X Y stage)))).rate epsilon ≤ stage
  rw [regularizedInnerRegularity_markov_left_rate_eq]
  have hpaid := centralPhysicalJointAdaptiveMarkov_inner_rates_paid
    (by decide) (by decide) 0 pointwise GX GY epsilon hepsilon
    (slowIndex (extraRequirement X Y) stage)
    (slowIndex_cofinal (extraRequirement X Y) _ stage hstage)
  exact Nat.le_trans hpaid.2.2 (slowIndex_le_stage (extraRequirement X Y) stage)

def reflectedCrossLimit : CReal :=
  cubeReflectedPairingLimit (sectorCauchyToReflected X) (sectorCauchyToReflected Y)

/-- The same sampled dense normalized forms converge to the reflected pairing. -/
theorem normalizedCross_converges :
    CReal.ConvergesTo (fun stage => CReal.ofQ'
      ((baseNormalized X Y (slowIndex (extraRequirement X Y) stage)).approx stage))
      (reflectedCrossLimit X Y) := by
  have hbase : CReal.ConvergesTo (baseNormalized X Y) (reflectedCrossLimit X Y) :=
    convergesTo_cofinalReindex
      (cubeReflectedPairingLimit_converges (sectorCauchyToReflected X) (sectorCauchyToReflected Y))
      (baseIndex X Y) (baseRate X Y)
      (centralPhysicalJointAdaptiveMarkovSampleIndex_cofinal (by decide) (by decide) 0 pointwise GX GY)
  apply diagonal_converges
    (convergesTo_cofinalReindex hbase (slowIndex (extraRequirement X Y))
      (slowThreshold (extraRequirement X Y)) (slowIndex_cofinal (extraRequirement X Y)))
    (fun stage => regularizedInnerRegularity
      (baseNormalizedRegularity X Y (slowIndex (extraRequirement X Y) stage)))
    (fun epsilon => slowThreshold (extraRequirement X Y) (CReal.lv epsilon))
  exact slow_regularized_rate_paid (baseNormalizedRegularity X Y) (extraRequirement X Y)
    (fun _ => Nat.le_max_right _ _)

/-- Literal finite equality once the computed admission requirement is paid. -/
theorem physicalCross_eq_normalized_approx (stage : Nat)
    (hstage : slowThreshold (extraRequirement X Y) 0 ≤ stage) :
    physicalCrossSequence X Y stage ≈
      (baseNormalized X Y (slowIndex (extraRequirement X Y) stage)).approx stage := by
  have hpaid := required_slowIndex_le (extraRequirement X Y) stage hstage
  have hadmit : realizationCutoff
      (presentationToCube (X.seq (stageIndex X Y stage)))
      (presentationToCube (Y.seq (stageIndex X Y stage))) ≤ stage :=
    Nat.le_trans (Nat.le_max_left _ _) hpaid
  have hfinite := cubeObservable_form_eq_normalized_approx
    (w := anchorCoupling) (by decide) (by decide)
    (presentationToCube (X.seq (stageIndex X Y stage)))
    (presentationToCube (Y.seq (stageIndex X Y stage))) stage hadmit
  rw [presentationToCube_observable, presentationToCube_observable] at hfinite
  exact Q'.eqv_trans _ _ _
    (innerLimit_markovCutoffAction_cross_approx_eqv_form (w := anchorCoupling)
      (by decide) (by decide) 0 stage _ _)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm
      (centralPhysicalMarkovApply_self_adjoint anchorCoupling (by decide) stage 0 _ _)) hfinite)

/-- The two already constructed limits are equal, not merely compatible. -/
theorem physicalCrossLimit_eq_reflected :
    CReal.Equiv (physicalCrossLimit X Y) (reflectedCrossLimit X Y) := by
  let index := fun n => max (slowThreshold (extraRequirement X Y) 0) n
  apply CReal.Equiv_of_limit_of_equal
    (aSeq := fun n => CReal.ofQ' (physicalCrossSequence X Y (index n)))
    (bSeq := fun n => CReal.ofQ'
      ((baseNormalized X Y (slowIndex (extraRequirement X Y) (index n))).approx (index n)))
  · intro n
    exact CReal.ofQ'_equiv_of_eqv (physicalCross_eq_normalized_approx X Y _ (Nat.le_max_left _ _))
  · exact convergesTo_cofinalReindex (physicalCross_converges X Y) index (fun n => n)
      (fun _ _ hn => Nat.le_trans hn (Nat.le_max_right _ _))
  · exact convergesTo_cofinalReindex (normalizedCross_converges X Y) index (fun n => n)
      (fun _ _ hn => Nat.le_trans hn (Nat.le_max_right _ _))

/-- Slowing the sampler leaves the physical completed operator unchanged. -/
theorem physicalCrossLimit_class :
    E (Quotient.mk (G).completionSetoid GX) (Quotient.mk (G).completionSetoid GY) =
      Quotient.mk CReal.crealSetoid (physicalCrossLimit X Y) := by
  have hT := centralPhysicalAdmissibleMarkovMap_class_eq_adaptive
    (by decide) (by decide) 0 pointwise GX (leftSample X Y)
  have hY := centralPhysicalAdmissibleMarkovInput_class_eq (rightSample X Y)
  unfold completedReflectedForm
  rw [← concrete_selfAdjoint]
  unfold centralPhysicalConcreteAdaptiveCompletedMarkovTransfer
  rw [centralPhysicalAdaptiveCompletedMarkovTransfer_mk, ← hT, hY]
  rfl

/-- The completed comparison preserves the SAME physical E pairing on its
ENTIRE marginal-sector source, not only on dense presentations. -/
theorem sectorToReflected_pairing (x y : (M).Completion) :
    cubeReflectedInner (sectorToReflected x) (sectorToReflected y) =
      E (centralPhysicalVacuumSectorCylinderCompletionToGlobal x)
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  change Quotient.mk CReal.crealSetoid (reflectedCrossLimit X Y) =
    E (Quotient.mk (G).completionSetoid (centralPhysicalVacuumSectorCylinderCauchyToGlobal X))
      (Quotient.mk (G).completionSetoid (centralPhysicalVacuumSectorCylinderCauchyToGlobal Y))
  rw [physicalCrossLimit_class]
  exact Quotient.sound (CReal.Equiv.symm (physicalCrossLimit_eq_reflected X Y))

local notation "TM" => centralPhysicalVacuumSectorCylinderCompletedTransfer
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "I" => centralPhysicalVacuumSectorCylinderCompletionToGlobal
  (hw0 := (by decide : (0 : Q') < anchorCoupling)) (hw1 := (by decide : anchorCoupling < (1 : Q')))
  (half := 0)

private theorem sectorTransfer_intertwines (x : (M).Completion) :
    I (TM x) = centralPhysicalConcreteAdaptiveCompletedMarkovTransfer
      (w := anchorCoupling) (by decide) (by decide) 0 (I x) :=
  (centralPhysicalVacuumSectorCylinderTransferLiftData (w := anchorCoupling)
    (by decide) (by decide) 0).intertwines x

/-- The actual sector action followed by the comparison. Its domain is still
the marginal sector; this is NOT yet an endomorphism of E completion. -/
def mappedTransfer (x : (M).Completion) : CubeReflectedCompletion := sectorToReflected (TM x)

theorem mappedTransfer_contraction (x : (M).Completion) :
    CReal.RCle (cubeReflectedInner (mappedTransfer x) (mappedTransfer x))
      (cubeReflectedInner (sectorToReflected x) (sectorToReflected x)) := by
  simp only [mappedTransfer, sectorToReflected_pairing, sectorTransfer_intertwines]
  exact completedReflectedForm_contraction (w := anchorCoupling) (by decide) (by decide) 0 (I x)

theorem mappedTransfer_selfAdjoint (x y : (M).Completion) :
    cubeReflectedInner (mappedTransfer x) (sectorToReflected y) =
      cubeReflectedInner (sectorToReflected x) (mappedTransfer y) := by
  simp only [mappedTransfer, sectorToReflected_pairing, sectorTransfer_intertwines]
  exact completedReflectedForm_transfer_selfAdjoint (w := anchorCoupling)
    (by decide) (by decide) 0 (I x) (I y)

theorem mappedTransfer_positive (x : (M).Completion) :
    CReal.RCnonneg (cubeReflectedInner (mappedTransfer x) (sectorToReflected x)) := by
  simp only [mappedTransfer, sectorToReflected_pairing, sectorTransfer_intertwines]
  exact completedReflectedForm_transfer_positive (w := anchorCoupling) (by decide) (by decide) 0 (I x)

/-- Same physical conditional iterations and the exact one-insertion shift;
no assertion that an iteration is geometric Euclidean time. -/
theorem sectorToReflected_moments (n : Nat) (x y : (M).Completion) :
    cubeReflectedInner (sectorToReflected x)
      (sectorToReflected (centralPhysicalVacuumSectorCylinderCompletedTransferPower
        (w := anchorCoupling) (by decide) (by decide) 0 n y)) =
      centralPhysicalCutoffCompletedInner (w := anchorCoupling) (by decide) (by decide) 0 (I x)
        (centralPhysicalConcreteAdaptiveCompletedMarkovPower
          (w := anchorCoupling) (by decide) (by decide) 0 (n + 1) (I y)) := by
  rw [sectorToReflected_pairing, centralPhysicalVacuumSectorCylinderCompletedTransferPower_intertwines]
  rfl

end YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing

#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing.baseIndex
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing.baseRate
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing.baseNormalized
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing.baseNormalizedRegularity
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing.extraRequirement
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing.stageIndex
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing.stageRate
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing.stageIndex_cofinal
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing.leftSample
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing.rightSample
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing.leftAction
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing.rightInput
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing.physicalCrossLimit
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing.physicalCrossSequence
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing.physicalCross_converges
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing.reflectedCrossLimit
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing.normalizedCross_converges
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing.physicalCross_eq_normalized_approx
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing.physicalCrossLimit_eq_reflected
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing.physicalCrossLimit_class
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing.sectorToReflected_pairing
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing.mappedTransfer
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing.mappedTransfer_contraction
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing.mappedTransfer_selfAdjoint
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing.mappedTransfer_positive
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing.sectorToReflected_moments
