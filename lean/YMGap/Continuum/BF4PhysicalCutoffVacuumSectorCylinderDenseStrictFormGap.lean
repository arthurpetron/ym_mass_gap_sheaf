/-
# The sector-local cofinal certificate controls the actual dense BF4 form

The moving centered diagonal and matrix limits have now been identified with
the actual completed norm and transfer form on every dense orthogonal
root-sector cylinder.  Therefore the existing sector-local cofinal strict-gap
certificate descends immediately to an `RCle` form inequality on that actual
dense completed carrier, at the same rational rate `q < 1`.

No inhabitant of the common-rate certificate is constructed here.  The result
is a conditional compiler on the dense orthogonal domain, not yet its closure
extension, a thermodynamic limit, continuum QFT, or the Clay theorem.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseCenteredFormIdentification
import YMGap.Continuum.RCScaleClose

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseStrictFormGap

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseCenteredFormIdentification
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift

/-- Any sector-local cofinal centered certificate at `q < 1` gives the same
strict form bound for every actual dense completed sector vector orthogonal to
the normalized global vacuum. -/
theorem centralPhysicalVacuumSectorCylinder_denseCompletedStrictFormGapAtRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {q : Q'}
    (certificate : FixedNomeCofinalVacuumSectorCenteredStrictGap
      w (Q'.le_of_lt hw0) half q)
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
      (CReal.RCscale q
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
  exact certificate.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
    hw0 hw1 half presentation.base presentation.coefficient

/-- The supplied certificate is genuinely strict: the dense completed form
bound above has a nonnegative rate below one. -/
theorem centralPhysicalVacuumSectorCylinder_denseCompletedStrictFormGapAtRate_rate
    {w : Q'} {hw0 : (0 : Q') < w}
    {half : Nat} {q : Q'}
    (certificate : FixedNomeCofinalVacuumSectorCenteredStrictGap
      w (Q'.le_of_lt hw0) half q) :
    (0 : Q') ≤ q ∧ q < (1 : Q') :=
  ⟨certificate.rate_nonnegative, certificate.rate_lt_one⟩

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseStrictFormGap

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseStrictFormGap.centralPhysicalVacuumSectorCylinder_denseCompletedStrictFormGapAtRate
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseStrictFormGap.centralPhysicalVacuumSectorCylinder_denseCompletedStrictFormGapAtRate_rate
