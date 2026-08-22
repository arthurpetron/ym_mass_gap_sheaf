/-
# Inhabiting the BF4 adaptive sector-recoding tail

The base-controlled representative pays the amplitude-scaled stationary shell
cutoff at every selected original index.  The outer adaptive sampler is
cofinal in the controlled sequence index, while the inner slow sampler is
cofinal in the original sequence index.

For requested tolerance `epsilon`, this file forces the outer sampler past
both the zeroth inner threshold and the threshold at `CReal.lv epsilon`.
Thus the selected original index `i` satisfies `CReal.lv epsilon <= i`, its
shell cutoff is below the action stage, and the core--shell theorem gives

`distance^2 <= 1/(i+1) <= 1/(lv epsilon + 1) <= epsilon`.

This inhabits the formerly conditional adaptive recoding-tail record and
therefore constructs the completed root-sector transfer lift.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderAdaptiveRecodingTail
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderRecodingCoreShell

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderAdaptiveRecodingTailInhabited

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionSchedule
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.BF4PhysicalCutoffStationarySourceTail
open YMGap.Continuum.BF4PhysicalCutoffTargetShellTail
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderAdaptiveRecodingTail
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderBaseControlledCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderRecodingCoreShell
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalDenseStageSlowDiagonalComparison
open YMGap.Continuum.CRealSeminormCompletion

/-! ## 1. The nested cofinal rate -/

/-- The controlled-sequence index which simultaneously admits the inner
zeroth requirement and forces the selected original index beyond the
rational precision associated to `epsilon`. -/
def centralPhysicalVacuumSectorAdaptiveRecodingTailAnchor
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') : Nat :=
  max
    (slowThreshold (centralPhysicalVacuumSectorBaseRequirement X) 0)
    (slowThreshold (centralPhysicalVacuumSectorBaseRequirement X)
      (CReal.lv epsilon))

/-- The outer adaptive rate which forces its selected controlled index past
the nested anchor. -/
def centralPhysicalVacuumSectorAdaptiveRecodingTailRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (epsilon : Q') : Nat :=
  centralPhysicalAdaptiveMarkovSampleRate hw0 hw1 half
    (centralPhysicalDenseMarkovCauchyData hw0 hw1 half)
    (centralPhysicalVacuumSectorCylinderCauchyToGlobal
      (centralPhysicalVacuumSectorBaseControlledCauchy X))
    (centralPhysicalVacuumSectorAdaptiveRecodingTailAnchor X epsilon)

/-! ## 2. Nested cofinality inhabits the tail -/

/-- The adaptive sector recoding converges unconditionally to the global
adaptive output. -/
def centralPhysicalVacuumSectorAdaptiveRecodingTailData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    CentralPhysicalVacuumSectorAdaptiveRecodingTailData hw0 hw1 half where
  rate := centralPhysicalVacuumSectorAdaptiveRecodingTailRate hw0 hw1 half
  close := by
    intro X epsilon hepsilon stage hstage
    let required := centralPhysicalVacuumSectorBaseRequirement X
    let precision := CReal.lv epsilon
    let anchor :=
      centralPhysicalVacuumSectorAdaptiveRecodingTailAnchor X epsilon
    let pointwise := centralPhysicalDenseMarkovCauchyData hw0 hw1 half
    let controlled := centralPhysicalVacuumSectorBaseControlledCauchy X
    let global := centralPhysicalVacuumSectorCylinderCauchyToGlobal controlled
    let sample := centralPhysicalVacuumSectorAdaptiveSampleIndex
      hw0 hw1 half pointwise X stage
    let index := centralPhysicalVacuumSectorBaseSampleIndex X sample
    have hanchorSample : anchor ≤ sample := by
      unfold sample centralPhysicalVacuumSectorAdaptiveSampleIndex
      apply centralPhysicalAdaptiveMarkovSampleIndex_cofinal
        hw0 hw1 half pointwise global anchor stage
      change centralPhysicalVacuumSectorAdaptiveRecodingTailRate
        hw0 hw1 half X epsilon ≤ stage at hstage
      unfold centralPhysicalVacuumSectorAdaptiveRecodingTailRate at hstage
      exact hstage
    have hzeroThreshold : slowThreshold required 0 ≤ sample :=
      Nat.le_trans
        (Nat.le_trans (Nat.le_max_left _ _) hanchorSample)
        (Nat.le_refl sample)
    have hprecisionThreshold : slowThreshold required precision ≤ sample :=
      Nat.le_trans
        (Nat.le_trans (Nat.le_max_right _ _) hanchorSample)
        (Nat.le_refl sample)
    have hprecisionIndex : precision ≤ index := by
      unfold index centralPhysicalVacuumSectorBaseSampleIndex
      exact slowIndex_cofinal required precision sample hprecisionThreshold
    have hinvSucc : Q'.invSucc index ≤ epsilon :=
      Q'.le_trans' _ _ _
        (ExpNeg.invSucc_le_of_le hprecisionIndex)
        (CReal.invSucc_lv_le hepsilon)
    have hsampleStage : sample ≤ stage := by
      unfold sample centralPhysicalVacuumSectorAdaptiveSampleIndex
      exact centralPhysicalAdaptiveMarkovSampleIndex_le_stage
        hw0 hw1 half pointwise global stage
    have hshellSample :=
      centralPhysicalVacuumSectorBaseControlled_shellCutoff_le_stage
        X sample hzeroThreshold
    have hshellStage :
        centralPhysicalTargetShellCutoff w half
            (centralPhysicalVacuumSectorPresentationShellTolerance
              (X.seq index) (Q'.invSucc index)) ≤ stage := by
      exact Nat.le_trans hshellSample hsampleStage
    have hinput :
        centralPhysicalVacuumSectorConcreteAdaptiveInput
            hw0 hw1 half X stage = X.seq index := by
      change (centralPhysicalVacuumSectorBaseControlledCauchy X).seq sample =
        X.seq index
      change centralPhysicalVacuumSectorBaseControlledSeq X sample =
        X.seq index
      unfold centralPhysicalVacuumSectorBaseControlledSeq
      rw [if_pos hzeroThreshold]
    have hbase := centralPhysicalVacuumSectorAdaptiveSample_base_le_stage
      hw0 hw1 half pointwise X stage
    have hshellInput :
        centralPhysicalTargetShellCutoff w half
            (centralPhysicalVacuumSectorPresentationShellTolerance
              (centralPhysicalVacuumSectorConcreteAdaptiveInput
                hw0 hw1 half X stage)
              (Q'.invSucc index)) ≤ stage := by
      rw [hinput]
      exact hshellStage
    have hbound :=
      centralPhysicalVacuumSectorRecoding_distSq_le_invSucc
        hw0 hw1 half stage index
        (centralPhysicalVacuumSectorConcreteAdaptiveInput
          hw0 hw1 half X stage)
        hbase hshellInput
    have htarget : CReal.leEv
        (CReal.ofQ' (Q'.invSucc index)) (CReal.ofQ' epsilon) :=
      CReal.leEv_of_le (CReal.ofQ'_le_ofQ' hinvSucc)
    rw [centralPhysicalVacuumSectorConcreteAdaptiveOutputObservable_eq_finite,
      centralPhysicalVacuumSectorConcreteAdaptiveGlobalOutputObservable_eq_action]
    exact CReal.leEv_trans hbound htarget

/-! ## 3. The unconditional completed sector transfer lift -/

/-- The proved tail compiles to a genuine transfer on the completed root
sector which intertwines the concrete global adaptive transfer. -/
def centralPhysicalVacuumSectorCylinderTransferLiftData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    CentralPhysicalVacuumSectorCylinderTransferLiftData hw0 hw1 half :=
  (centralPhysicalVacuumSectorAdaptiveRecodingTailData
    hw0 hw1 half).toTransferLiftData

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderAdaptiveRecodingTailInhabited

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderAdaptiveRecodingTailInhabited.centralPhysicalVacuumSectorAdaptiveRecodingTailData
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderAdaptiveRecodingTailInhabited.centralPhysicalVacuumSectorCylinderTransferLiftData
