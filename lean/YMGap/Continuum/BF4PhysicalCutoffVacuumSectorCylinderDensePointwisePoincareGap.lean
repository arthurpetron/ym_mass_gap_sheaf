/-
# The explicit fixed-base Poincare gap reaches the actual dense BF4 sector

The canonical physical vacuum-sector cylinder completion is the closure of
finite root-component presentations.  For each such presentation, the
constructed persistent positive-edge floor already gives one rational
Poincare rate below one, uniform in all later representation cutoffs.  The
moving centered form limits have also been identified with the actual norm
and transfer form of the embedded completed vector.

This module composes those two inhabited results.  Every dense cylinder
orthogonal to the vacuum obeys the actual completed strict form interval at
the rate belonging to its own finite base carrier.  The rate remains visibly
base-dependent.  In particular this is not a common rate on the closure, a
thermodynamic or continuum gap, or the Clay theorem.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, trusted external computation, or enlarged
heartbeat budget is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloorFormula
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformCRealGap
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedStrictFormGap
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseCenteredFormIdentification

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDensePointwisePoincareGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedStrictFormGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseCenteredFormIdentification
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloorFormula
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformCRealGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap

/-! ## 1. The rate attached to one dense cylinder base -/

/-- The constructed later-cutoff-uniform Poincare rate belonging to the
finite base carrier of one sector-cylinder presentation. -/
def centralPhysicalVacuumSectorCylinderDensePoincareRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half) : Q' :=
  FixedBasePulledPositiveEdgeFloor.uniformPoincareRate
    (explicitFixedBasePulledPositiveEdgeFloor
      hw0 hw1 presentation.base half)

theorem centralPhysicalVacuumSectorCylinderDensePoincareRate_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half) :
    (0 : Q') ≤
      centralPhysicalVacuumSectorCylinderDensePoincareRate
        hw0 hw1 half presentation := by
  unfold centralPhysicalVacuumSectorCylinderDensePoincareRate
  exact FixedBasePulledPositiveEdgeFloor.uniformPoincareRate_nonnegative _

theorem centralPhysicalVacuumSectorCylinderDensePoincareRate_lt_one
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half) :
    centralPhysicalVacuumSectorCylinderDensePoincareRate
        hw0 hw1 half presentation < (1 : Q') := by
  unfold centralPhysicalVacuumSectorCylinderDensePoincareRate
  exact FixedBasePulledPositiveEdgeFloor.uniformPoincareRate_lt_one _

/-! ## 2. Actual completed form interval on the dense cylinder -/

/-- The fixed-base cutoff-limit Poincare estimate is exactly the upper form
bound for the corresponding embedded vector in the actual completed sector. -/
theorem centralPhysicalVacuumSectorCylinder_denseCompletedFormGap
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half)
    (horthogonal : CentralPhysicalVacuumSectorCylinderGlobalVacuumOrthogonal
      hw0 hw1 half
      ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
        hw0 hw1 half).embedRep presentation)) :
    CReal.RCle
      (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCompletedTransfer hw0 hw1 half
          ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).embedRep presentation))
        ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
          hw0 hw1 half).embedRep presentation))
      (CReal.RCscale
        (centralPhysicalVacuumSectorCylinderDensePoincareRate
          hw0 hw1 half presentation)
        (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
          ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).embedRep presentation)
          ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).embedRep presentation))) := by
  rw [centralPhysicalVacuumSectorCylinder_completedTransferForm_embedRep_eq_centered
    hw0 hw1 half presentation horthogonal]
  unfold centralPhysicalVacuumSectorCylinderCompletedInner
  rw [centralPhysicalVacuumSectorCylinder_completedInner_embedRep_eq_centered
    hw0 hw1 half presentation horthogonal]
  rw [CReal.RCscale_mk, CReal.RCle_mk]
  unfold centralPhysicalVacuumSectorCylinderDensePoincareRate
  exact centeredMatrixCutoffLimit_leEv_uniformPoincareRate_mul_diagonal
    hw0 hw1 presentation.base half
    (explicitFixedBasePulledPositiveEdgeFloor
      hw0 hw1 presentation.base half)
    presentation.coefficient

/-- Every dense vacuum-orthogonal sector cylinder therefore has an inhabited
positive strict form interval on the actual completed carrier.  The explicit
rate is indexed by `presentation.base`. -/
theorem centralPhysicalVacuumSectorCylinder_denseCompletedStrictFormInterval
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half)
    (horthogonal : CentralPhysicalVacuumSectorCylinderGlobalVacuumOrthogonal
      hw0 hw1 half
      ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
        hw0 hw1 half).embedRep presentation)) :
    let vector :=
      (centralPhysicalVacuumSectorCylinderSquaredSeminorm
        hw0 hw1 half).embedRep presentation
    let rate := centralPhysicalVacuumSectorCylinderDensePoincareRate
      hw0 hw1 half presentation
    let form := centralPhysicalVacuumSectorCylinderCompletedInner
      hw0 hw1 half
      (centralPhysicalVacuumSectorCylinderCompletedTransfer
        hw0 hw1 half vector) vector
    let norm := centralPhysicalVacuumSectorCylinderCompletedInner
      hw0 hw1 half vector vector
    CReal.RCnonneg form ∧
      CReal.RCle form (CReal.RCscale rate norm) ∧
        rate < (1 : Q') := by
  dsimp only
  exact
    ⟨centralPhysicalVacuumSectorCylinder_completedTransferForm_nonnegative
        hw0 hw1 half
        ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
          hw0 hw1 half).embedRep presentation),
      centralPhysicalVacuumSectorCylinder_denseCompletedFormGap
        hw0 hw1 half presentation horthogonal,
      centralPhysicalVacuumSectorCylinderDensePoincareRate_lt_one
        hw0 hw1 half presentation⟩

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDensePointwisePoincareGap

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDensePointwisePoincareGap.centralPhysicalVacuumSectorCylinderDensePoincareRate
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDensePointwisePoincareGap.centralPhysicalVacuumSectorCylinderDensePoincareRate_lt_one
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDensePointwisePoincareGap.centralPhysicalVacuumSectorCylinder_denseCompletedFormGap
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDensePointwisePoincareGap.centralPhysicalVacuumSectorCylinder_denseCompletedStrictFormInterval
