/-
# Outer raw diagonal convergence for arbitrary completed BF4 sector vectors

For a sector Cauchy representative, take the pulled diagonal cutoff limit of
each dense term.  These Bishop reals converge to the same outer pairing limit
that represents the actual completed squared norm of the quotient class.

This supplies the uncentered diagonal half of the arbitrary-completion
centered-form cofinality bridge.  The remaining step must compare these raw
diagonals with the moving head-centered diagonals using the already-proved
outer head-correction convergence.  No matrix-form, common strict-rate,
thermodynamic, continuum, or Clay claim is made here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Constructive.TrigAddCReal
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterHeadCorrectionVanishing

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRawDiagonal

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy

/-! ## 1. The outer raw diagonal sequence -/

def centralPhysicalVacuumSectorCylinderOuterPulledDiagonalSeq
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) (stage : Nat) : CReal :=
  centralPhysicalFinitePulledVacuumSectorDiagonalQuadraticCutoffLimit
    hw0 hw1 (X.seq stage).base half (X.seq stage).coefficient

/-! ## 2. Convergence and completed-norm identification -/

/-- The outer pulled raw diagonals of the dense representative terms converge
to the representative's actual global completed pairing limit. -/
theorem centralPhysicalVacuumSectorCylinder_outerPulledDiagonal_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    CReal.ConvergesTo
      (centralPhysicalVacuumSectorCylinderOuterPulledDiagonalSeq X)
      (physicalCauchyPairingLimit hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCauchyToGlobal X)
        (centralPhysicalVacuumSectorCylinderCauchyToGlobal X)) := by
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (s := physicalCauchyPairingSeq hw0 hw1 half
      (centralPhysicalVacuumSectorCylinderCauchyToGlobal X)
      (centralPhysicalVacuumSectorCylinderCauchyToGlobal X))
  · intro stage
    change CReal.Equiv
      (innerLimit hw0 hw1 half
        (X.seq stage).toLinearObservable
        (X.seq stage).toLinearObservable)
      (centralPhysicalFinitePulledVacuumSectorDiagonalQuadraticCutoffLimit
        hw0 hw1 (X.seq stage).base half (X.seq stage).coefficient)
    exact centralPhysicalVacuumSectorCylinder_innerLimit_equiv_pulledDiagonal
      hw0 hw1 half (X.seq stage)
  · exact physicalCauchyPairingSeq_converges hw0 hw1 half
      (centralPhysicalVacuumSectorCylinderCauchyToGlobal X)
      (centralPhysicalVacuumSectorCylinderCauchyToGlobal X)

/-- The target of outer raw diagonal convergence represents the actual
completed sector squared norm of the quotient class of the representative. -/
theorem centralPhysicalVacuumSectorCylinder_completedInner_mk_eq_outerRawDiagonalLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
        (Quotient.mk
          (centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).completionSetoid X)
        (Quotient.mk
          (centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).completionSetoid X) =
      Quotient.mk CReal.crealSetoid
        (physicalCauchyPairingLimit hw0 hw1 half
          (centralPhysicalVacuumSectorCylinderCauchyToGlobal X)
          (centralPhysicalVacuumSectorCylinderCauchyToGlobal X)) := rfl

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRawDiagonal

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRawDiagonal.centralPhysicalVacuumSectorCylinder_outerPulledDiagonal_converges
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRawDiagonal.centralPhysicalVacuumSectorCylinder_completedInner_mk_eq_outerRawDiagonalLimit
