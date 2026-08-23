/-
# Dense BF4 centered form limits are the actual completed sector forms

On a dense completed root-sector cylinder orthogonal to the global vacuum,
the moving head correction is now known to vanish as a Bishop real.  The
existing exact polynomial expansions then show that the moving centered
diagonal and reflected-form limits equal their uncentered pulled limits.
Combining those identities with the completed norm and transfer-form bridges
identifies both moving centered limits with the actual completed forms.

This closes the form-identification edge on dense orthogonal sector vectors.
It does not yet extend the comparison to arbitrary completed sector vectors,
construct one carrier-independent strict rate, or supply thermodynamic or
continuum control.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Constructive.CRealExp
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseHeadCorrectionVanishing
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseTransferForm

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseCenteredFormIdentification

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.CRealAlg
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseHeadCorrectionVanishing
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseTransferForm
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector

/-! ## 1. Small constructive-real algebra -/

private theorem creal_neg_czero :
    CReal.Equiv (CReal.neg CReal.czero) CReal.czero :=
  SumOfSquares.Equiv_of_approx_eqv (fun _ =>
    (by decide : (-(0 : Q')).eqv 0))

private theorem creal_add_czero (value : CReal) :
    CReal.Equiv (CReal.add value CReal.czero) value :=
  SumOfSquares.Equiv_of_approx_eqv (fun stage =>
    Q'.eqv_of_eq (Q'.add_zero' (value.approx stage)))

private theorem creal_zero_mul (value : CReal) :
    CReal.Equiv (CReal.mul CReal.czero value) CReal.czero :=
  SumOfSquares.Equiv_of_approx_eqv (fun stage =>
    Q'.zero_mul_eqv (value.approx stage))

private theorem creal_add_neg_self (value : CReal) :
    CReal.Equiv (CReal.add value (CReal.neg value)) CReal.czero :=
  SumOfSquares.Equiv_of_approx_eqv (fun stage =>
    Q'.add_neg_self_eqv (value.approx stage))

private theorem creal_mul_congr_right
    {left right right' : CReal} (h : CReal.Equiv right right') :
    CReal.Equiv (CReal.mul left right) (CReal.mul left right') :=
  (CRealAlg.cmul_comm left right).trans
    ((CReal.mul_congr_left h).trans (CRealAlg.cmul_comm right' left))

private theorem creal_add_neg_equiv_zero_of_equiv
    {left right : CReal} (h : CReal.Equiv left right) :
    CReal.Equiv (CReal.add left (CReal.neg right)) CReal.czero :=
  (CReal.add_congr_left h).trans (creal_add_neg_self right)

private theorem creal_add_equiv_zero_of_both
    {left right : CReal}
    (hleft : CReal.Equiv left CReal.czero)
    (hright : CReal.Equiv right CReal.czero) :
    CReal.Equiv (CReal.add left right) CReal.czero :=
  (CReal.add_congr_left hleft).trans
    ((CReal.add_congr_right hright).trans (creal_add_czero CReal.czero))

/-! ## 2. Centered polynomial limits contract to the raw forms -/

/-- Pointwise recoding does not change the Bishop real represented by the
moving centered diagonal sequence. -/
theorem centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonal_equiv_expansion
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat → Q') :
    CReal.Equiv
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
        hw0 hw1 base half coefficient)
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalExpansionCutoffLimit
        hw0 hw1 base half coefficient) :=
  SumOfSquares.Equiv_of_approx_eqv (fun later =>
    centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonal_eqv_expansionApprox
      hw0 hw1 base half coefficient later)

/-- If the head-correction limit is zero, the moving centered diagonal limit
is the uncentered pulled diagonal limit. -/
theorem centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonal_equiv_raw_of_correction_zero
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat → Q')
    (hcorrection : CReal.Equiv
      (centralPhysicalFinitePulledVacuumSectorHeadCorrectionCutoffLimit
        hw0 hw1 base half coefficient)
      CReal.czero) :
    CReal.Equiv
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
        hw0 hw1 base half coefficient)
      (centralPhysicalFinitePulledVacuumSectorDiagonalQuadraticCutoffLimit
        hw0 hw1 base half coefficient) := by
  let correction :=
    centralPhysicalFinitePulledVacuumSectorHeadCorrectionCutoffLimit
      hw0 hw1 base half coefficient
  let root := CReal.ofQ' (coefficient 0)
  let centeredRoot := CReal.add root (CReal.neg correction)
  let oldRootSquare := CReal.ofQ' (coefficient 0 * coefficient 0)
  let raw := centralPhysicalFinitePulledVacuumSectorDiagonalQuadraticCutoffLimit
    hw0 hw1 base half coefficient
  let rootWeight := centralPhysicalFinitePulledWeightCutoffLimit
    hw0 hw1 base half 0
    (centralPhysicalFiniteVacuumSectorIndex_lt
      w (Q'.le_of_lt hw0) base half
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw0) base half))
  have hneg : CReal.Equiv (CReal.neg correction) CReal.czero :=
    (CReal.neg_congr hcorrection).trans creal_neg_czero
  have hcenteredRoot : CReal.Equiv centeredRoot root :=
    (CReal.add_congr_right hneg).trans (creal_add_czero root)
  have hsquare :
      CReal.Equiv (CReal.mul centeredRoot centeredRoot) oldRootSquare :=
    ((CReal.mul_congr_left hcenteredRoot).trans
      (creal_mul_congr_right hcenteredRoot)).trans
      (CReal.Equiv.symm (CRealAlg.ofQ'_mul (coefficient 0) (coefficient 0)))
  have hbracket : CReal.Equiv
      (CReal.add (CReal.mul centeredRoot centeredRoot)
        (CReal.neg oldRootSquare)) CReal.czero :=
    creal_add_neg_equiv_zero_of_equiv hsquare
  have htail : CReal.Equiv
      (CReal.mul
        (CReal.add (CReal.mul centeredRoot centeredRoot)
          (CReal.neg oldRootSquare))
        rootWeight) CReal.czero :=
    (CReal.mul_congr_left hbracket).trans (creal_zero_mul rootWeight)
  refine
    (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonal_equiv_expansion
      hw0 hw1 base half coefficient).trans ?_
  change CReal.Equiv
    (CReal.add raw
      (CReal.mul
        (CReal.add (CReal.mul centeredRoot centeredRoot)
          (CReal.neg oldRootSquare))
        rootWeight)) raw
  exact (CReal.add_congr_right htail).trans (creal_add_czero raw)

/-- Pointwise recoding does not change the Bishop real represented by the
moving centered reflected quadratic. -/
theorem centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrix_equiv_expansion
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat → Q') :
    CReal.Equiv
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
        hw0 hw1 base half coefficient)
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixExpansionCutoffLimit
        hw0 hw1 base half coefficient) :=
  SumOfSquares.Equiv_of_approx_eqv (fun later =>
    centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrix_eqv_expansionApprox
      hw0 hw1 base half coefficient later)

/-- If the head-correction limit is zero, the moving centered reflected-form
limit is the uncentered pulled matrix limit. -/
theorem centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrix_equiv_raw_of_correction_zero
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat → Q')
    (hcorrection : CReal.Equiv
      (centralPhysicalFinitePulledVacuumSectorHeadCorrectionCutoffLimit
        hw0 hw1 base half coefficient)
      CReal.czero) :
    CReal.Equiv
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
        hw0 hw1 base half coefficient)
      (centralPhysicalFinitePulledVacuumSectorMatrixQuadraticCutoffLimit
        hw0 hw1 base half coefficient) := by
  let correction :=
    centralPhysicalFinitePulledVacuumSectorHeadCorrectionCutoffLimit
      hw0 hw1 base half coefficient
  let shift := CReal.neg correction
  let raw := centralPhysicalFinitePulledVacuumSectorMatrixQuadraticCutoffLimit
    hw0 hw1 base half coefficient
  let rightCross :=
    centralPhysicalFinitePulledVacuumSectorMatrixBilinearCutoffLimit
      hw0 hw1 base half coefficient finiteRootIndicator
  let leftCross :=
    centralPhysicalFinitePulledVacuumSectorMatrixBilinearCutoffLimit
      hw0 hw1 base half finiteRootIndicator coefficient
  let rootRoot :=
    centralPhysicalFinitePulledVacuumSectorMatrixBilinearCutoffLimit
      hw0 hw1 base half finiteRootIndicator finiteRootIndicator
  have hshift : CReal.Equiv shift CReal.czero :=
    (CReal.neg_congr hcorrection).trans creal_neg_czero
  have hright : CReal.Equiv (CReal.mul shift rightCross) CReal.czero :=
    (CReal.mul_congr_left hshift).trans (creal_zero_mul rightCross)
  have hleft : CReal.Equiv (CReal.mul shift leftCross) CReal.czero :=
    (CReal.mul_congr_left hshift).trans (creal_zero_mul leftCross)
  have hshiftSquare :
      CReal.Equiv (CReal.mul shift shift) CReal.czero :=
    (CReal.mul_congr_left hshift).trans (creal_zero_mul shift)
  have hroot :
      CReal.Equiv (CReal.mul (CReal.mul shift shift) rootRoot) CReal.czero :=
    (CReal.mul_congr_left hshiftSquare).trans (creal_zero_mul rootRoot)
  have hinner : CReal.Equiv
      (CReal.add (CReal.mul shift leftCross)
        (CReal.mul (CReal.mul shift shift) rootRoot)) CReal.czero :=
    creal_add_equiv_zero_of_both hleft hroot
  have htail : CReal.Equiv
      (CReal.add (CReal.mul shift rightCross)
        (CReal.add (CReal.mul shift leftCross)
          (CReal.mul (CReal.mul shift shift) rootRoot))) CReal.czero :=
    creal_add_equiv_zero_of_both hright hinner
  refine
    (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrix_equiv_expansion
      hw0 hw1 base half coefficient).trans ?_
  change CReal.Equiv
    (CReal.add raw
      (CReal.add (CReal.mul shift rightCross)
        (CReal.add (CReal.mul shift leftCross)
          (CReal.mul (CReal.mul shift shift) rootRoot)))) raw
  exact (CReal.add_congr_right htail).trans (creal_add_czero raw)

/-! ## 3. Identification with the actual completed forms -/

/-- For a dense completed sector vector orthogonal to the global vacuum, its
actual completed squared norm is the moving exactly centered diagonal limit. -/
theorem centralPhysicalVacuumSectorCylinder_completedInner_embedRep_eq_centered
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half)
    (horthogonal : CentralPhysicalVacuumSectorCylinderGlobalVacuumOrthogonal
      hw0 hw1 half
      ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
        hw0 hw1 half).embedRep presentation)) :
    centralPhysicalCutoffCompletedInner hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal
          ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).embedRep presentation))
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal
          ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).embedRep presentation)) =
      Quotient.mk CReal.crealSetoid
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
          hw0 hw1 presentation.base half presentation.coefficient) := by
  have hcorrection :=
    centralPhysicalVacuumSectorCylinder_headCorrection_equiv_zero_of_orthogonal
      hw0 hw1 half presentation horthogonal
  exact Eq.trans
    (centralPhysicalVacuumSectorCylinder_completedInner_embedRep_eq_pulled
      hw0 hw1 half presentation)
    (Quotient.sound (CReal.Equiv.symm
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonal_equiv_raw_of_correction_zero
        hw0 hw1 presentation.base half presentation.coefficient hcorrection)))

/-- For a dense completed sector vector orthogonal to the global vacuum, its
actual completed transfer form is the moving exactly centered matrix limit. -/
theorem centralPhysicalVacuumSectorCylinder_completedTransferForm_embedRep_eq_centered
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half)
    (horthogonal : CentralPhysicalVacuumSectorCylinderGlobalVacuumOrthogonal
      hw0 hw1 half
      ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
        hw0 hw1 half).embedRep presentation)) :
    centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCompletedTransfer hw0 hw1 half
          ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).embedRep presentation))
        ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
          hw0 hw1 half).embedRep presentation) =
      Quotient.mk CReal.crealSetoid
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit
          hw0 hw1 presentation.base half presentation.coefficient) := by
  have hcorrection :=
    centralPhysicalVacuumSectorCylinder_headCorrection_equiv_zero_of_orthogonal
      hw0 hw1 half presentation horthogonal
  exact Eq.trans
    (centralPhysicalVacuumSectorCylinder_completedTransferForm_embedRep_eq_pulled
      hw0 hw1 half presentation)
    (Quotient.sound (CReal.Equiv.symm
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrix_equiv_raw_of_correction_zero
        hw0 hw1 presentation.base half presentation.coefficient hcorrection)))

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseCenteredFormIdentification

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseCenteredFormIdentification.centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonal_equiv_raw_of_correction_zero
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseCenteredFormIdentification.centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrix_equiv_raw_of_correction_zero
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseCenteredFormIdentification.centralPhysicalVacuumSectorCylinder_completedInner_embedRep_eq_centered
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseCenteredFormIdentification.centralPhysicalVacuumSectorCylinder_completedTransferForm_embedRep_eq_centered
