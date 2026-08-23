/-
# The exact centered-form cofinality frontier for the completed BF4 sector

The sector-local strict estimate is now an actual completed form bound on the
dense orthogonal domain.  Extending it to every vector in the completed
sector vacuum complement requires a constructive diagonal approximation by
moving centered finite-sector forms.  This file packages exactly that
remaining completion datum and proves that it is sufficient.

The datum is inhabited unconditionally for every already-dense orthogonal
sector vector.  A global inhabitant for all completed sector vacuum vectors
is not asserted: constructing it is the current completion frontier.  The
common sector-local strict rate remains an independent analytic frontier.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseStrictFormGap
import YMGap.Continuum.FCNormBoundLimit

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedCenteredFormCofinality

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseCenteredFormIdentification
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseStrictFormGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift

/-! ## 1. The precise completion datum -/

/-- A cofinal family of moving centered finite-sector forms representing the
actual completed norm and transfer form of one sector vector. -/
structure CentralPhysicalVacuumSectorCylinderCenteredFormLimitData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (vector : CentralPhysicalCutoffVacuumSectorCylinderCompletion
      hw0 hw1 half) : Type 1 where
  presentation : Nat → CentralPhysicalVacuumSectorCylinderPresentation
    w (Q'.le_of_lt hw0) half
  normLimit : CReal
  formLimit : CReal
  diagonal_converges : CReal.ConvergesTo
    (fun stage =>
      centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
        hw0 hw1 (presentation stage).base half
          (presentation stage).coefficient)
    normLimit
  matrix_converges : CReal.ConvergesTo
    (fun stage =>
      centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
        hw0 hw1 (presentation stage).base half
          (presentation stage).coefficient)
    formLimit
  norm_identifies :
    centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
        vector vector =
      Quotient.mk CReal.crealSetoid normLimit
  form_identifies :
    centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCompletedTransfer
          hw0 hw1 half vector)
        vector =
      Quotient.mk CReal.crealSetoid formLimit

/-- The exact all-vector completion frontier: every actual completed sector
vacuum vector admits the centered-form limit data above. -/
structure CentralPhysicalVacuumSectorCylinderCompletedCenteredFormCofinality
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : Type 1 where
  centered : ∀ vector :
      CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
        hw0 hw1 half,
    CentralPhysicalVacuumSectorCylinderCenteredFormLimitData
      hw0 hw1 half vector.1

/-! ## 2. The datum is already inhabited on the dense orthogonal domain -/

/-- Constant outer approximation inhabits the cofinality datum for every
dense root-sector cylinder already orthogonal in the actual completion. -/
def centralPhysicalVacuumSectorCylinder_denseCenteredFormLimitData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half)
    (horthogonal : CentralPhysicalVacuumSectorCylinderGlobalVacuumOrthogonal
      hw0 hw1 half
      ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
        hw0 hw1 half).embedRep presentation)) :
    CentralPhysicalVacuumSectorCylinderCenteredFormLimitData
      hw0 hw1 half
      ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
        hw0 hw1 half).embedRep presentation) where
  presentation := fun _ => presentation
  normLimit :=
    centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
      hw0 hw1 presentation.base half presentation.coefficient
  formLimit :=
    centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
      hw0 hw1 presentation.base half presentation.coefficient
  diagonal_converges := CReal.convergesTo_const _
  matrix_converges := CReal.convergesTo_const _
  norm_identifies :=
    centralPhysicalVacuumSectorCylinder_completedInner_embedRep_eq_centered
      hw0 hw1 half presentation horthogonal
  form_identifies :=
    centralPhysicalVacuumSectorCylinder_completedTransferForm_embedRep_eq_centered
      hw0 hw1 half presentation horthogonal

/-! ## 3. Cofinality plus one strict sector rate closes the all-vector form -/

/-- The exact centered-form cofinality datum and one sector-local cofinal
strict rate give the actual completed strict form bound on every vector in the
sector vacuum complement. -/
theorem centralPhysicalVacuumSectorCylinder_completedStrictFormGapAtRate
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) {q : Q'}
    (certificate : FixedNomeCofinalVacuumSectorCenteredStrictGap
      w (Q'.le_of_lt hw0) half q)
    (cofinality :
      CentralPhysicalVacuumSectorCylinderCompletedCenteredFormCofinality
        hw0 hw1 half)
    (vector : CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
      hw0 hw1 half) :
    CReal.RCle
      (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer
          hw0 hw1 half vector).1 vector.1)
      (CReal.RCscale q
        (centralPhysicalVacuumSectorCylinderCompletedInner
          hw0 hw1 half vector.1 vector.1)) := by
  let data := cofinality.centered vector
  change CReal.RCle
    (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
      (centralPhysicalVacuumSectorCylinderCompletedTransfer
        hw0 hw1 half vector.1) vector.1)
    (CReal.RCscale q
      (centralPhysicalVacuumSectorCylinderCompletedInner
        hw0 hw1 half vector.1 vector.1))
  rw [data.form_identifies, data.norm_identifies,
    CReal.RCscale_mk, CReal.RCle_mk]
  apply CReal.leEv_of_convergesTo_le
    data.matrix_converges
    (CReal.convergesTo_constMul q data.diagonal_converges)
  intro stage
  exact certificate.centeredMatrixCutoffLimit_leEv_rate_mul_diagonal
    hw0 hw1 half
    (data.presentation stage).base
    (data.presentation stage).coefficient

/-- The resulting all-vector completed form rate retains the certificate's
nonnegativity and strictness. -/
theorem centralPhysicalVacuumSectorCylinder_completedStrictFormGapAtRate_rate
    {w : Q'} {hw0 : (0 : Q') < w}
    {half : Nat} {q : Q'}
    (certificate : FixedNomeCofinalVacuumSectorCenteredStrictGap
      w (Q'.le_of_lt hw0) half q) :
    (0 : Q') ≤ q ∧ q < (1 : Q') :=
  ⟨certificate.rate_nonnegative, certificate.rate_lt_one⟩

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedCenteredFormCofinality

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedCenteredFormCofinality.centralPhysicalVacuumSectorCylinder_denseCenteredFormLimitData
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedCenteredFormCofinality.centralPhysicalVacuumSectorCylinder_completedStrictFormGapAtRate
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedCenteredFormCofinality.centralPhysicalVacuumSectorCylinder_completedStrictFormGapAtRate_rate
