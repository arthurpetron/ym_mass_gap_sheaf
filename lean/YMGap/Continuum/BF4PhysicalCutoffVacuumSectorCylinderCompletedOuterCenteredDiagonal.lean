/-
# Outer centered diagonal convergence for completed BF4 sector vectors

For an arbitrary Cauchy representative of an actual completed sector vacuum
vector, the raw pulled diagonals already converge to its completed squared
norm and the moving head corrections already converge to zero.  The remaining
root coefficient is now known to converge as well.  The exact finite
root-replacement polynomial therefore tends to zero, while the pulled root
weight is canonically independent of the presentation base.

Consequently the outer sequence of moving head-centered diagonal cutoff-limit
Bishop reals converges to the same representative pairing limit as the raw
diagonal sequence.  This closes the diagonal half of the arbitrary-vector
centered-form cofinality datum.  The matrix half, a common strict rate, and all
thermodynamic, continuum, and Clay claims remain open.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRootCoordinate
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterCenteredDiagonal

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.CRealAlg
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterHeadCorrectionVanishing
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRawDiagonal
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRootCoordinate
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseCenteredFormIdentification
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Small constructive-real identities -/

private theorem creal_neg_czero :
    CReal.Equiv (CReal.neg CReal.czero) CReal.czero :=
  Equiv_of_approx_eqv (fun _ => (by decide : (-(0 : Q')).eqv 0))

private theorem creal_add_czero (value : CReal) :
    CReal.Equiv (CReal.add value CReal.czero) value :=
  Equiv_of_approx_eqv (fun stage =>
    Q'.eqv_of_eq (Q'.add_zero' (value.approx stage)))

private theorem creal_zero_mul (value : CReal) :
    CReal.Equiv (CReal.mul CReal.czero value) CReal.czero :=
  Equiv_of_approx_eqv (fun stage => Q'.zero_mul_eqv (value.approx stage))

private theorem creal_add_neg_self (value : CReal) :
    CReal.Equiv (CReal.add value (CReal.neg value)) CReal.czero :=
  Equiv_of_approx_eqv (fun stage => Q'.add_neg_self_eqv (value.approx stage))

/-! ## 2. Outer centered diagonal and root-weight sequences -/

def centralPhysicalVacuumSectorCylinderOuterHeadCenteredDiagonalSeq
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) (stage : Nat) : CReal :=
  centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit
    hw0 hw1 (X.seq stage).base half (X.seq stage).coefficient

def centralPhysicalVacuumSectorCylinderOuterRootWeightSeq
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) (stage : Nat) : CReal :=
  centralPhysicalFinitePulledWeightCutoffLimit
    hw0 hw1 (X.seq stage).base half 0
    (centralPhysicalFiniteVacuumSectorIndex_lt
      w (Q'.le_of_lt hw0) (X.seq stage).base half
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw0) (X.seq stage).base half))

/-- A single canonical root-weight limit, chosen at base cutoff zero. -/
def centralPhysicalVacuumSectorCylinderCanonicalRootWeightLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : CReal :=
  centralPhysicalFinitePulledWeightCutoffLimit
    hw0 hw1 0 half 0
    (centralPhysicalFiniteVacuumSectorIndex_lt
      w (Q'.le_of_lt hw0) 0 half
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw0) 0 half))

/-- The pulled vacuum-root weight does not depend on the source presentation
base: every cutoff embedding fixes index zero. -/
theorem centralPhysicalVacuumSectorCylinder_rootWeight_equiv_canonical
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half) :
    CReal.Equiv
      (centralPhysicalFinitePulledWeightCutoffLimit
        hw0 hw1 presentation.base half 0
        (centralPhysicalFiniteVacuumSectorIndex_lt
          w (Q'.le_of_lt hw0) presentation.base half
          (zero_mem_centralPhysicalFiniteVacuumSectorIndices
            w (Q'.le_of_lt hw0) presentation.base half)))
      (centralPhysicalVacuumSectorCylinderCanonicalRootWeightLimit
        hw0 hw1 half) := by
  apply Equiv_of_approx_eqv
  intro later
  change centralPhysicalFinitePulledWeight
      w (Q'.le_of_lt hw0) presentation.base later half 0 ≈
    centralPhysicalFinitePulledWeight
      w (Q'.le_of_lt hw0) 0 later half 0
  unfold centralPhysicalFinitePulledWeight
  rw [centralPhysicalFiniteCutoffIndexMap_zero,
    centralPhysicalFiniteCutoffIndexMap_zero]
  exact Q'.eqv_refl _

/-- The varying outer root-weight sequence is termwise the canonical fixed
root weight, and hence converges to it. -/
theorem centralPhysicalVacuumSectorCylinder_outerRootWeight_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    CReal.ConvergesTo
      (centralPhysicalVacuumSectorCylinderOuterRootWeightSeq X)
      (centralPhysicalVacuumSectorCylinderCanonicalRootWeightLimit
        hw0 hw1 half) := by
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (s := fun _ =>
      centralPhysicalVacuumSectorCylinderCanonicalRootWeightLimit
        hw0 hw1 half)
  · intro stage
    exact CReal.Equiv.symm
      (centralPhysicalVacuumSectorCylinder_rootWeight_equiv_canonical
        hw0 hw1 half (X.seq stage))
  · exact CReal.convergesTo_const _

/-! ## 3. The centered-minus-raw polynomial vanishes -/

/-- On an arbitrary representative of a completed vacuum-orthogonal sector
vector, moving head-centered diagonals converge to the same actual pairing
limit as the raw diagonals. -/
theorem centralPhysicalVacuumSectorCylinder_outerHeadCenteredDiagonal_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (horthogonal : CentralPhysicalVacuumSectorCylinderGlobalVacuumOrthogonal
      hw0 hw1 half
      (Quotient.mk
        (centralPhysicalVacuumSectorCylinderSquaredSeminorm
          hw0 hw1 half).completionSetoid X)) :
    CReal.ConvergesTo
      (centralPhysicalVacuumSectorCylinderOuterHeadCenteredDiagonalSeq X)
      (physicalCauchyPairingLimit hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCauchyToGlobal X)
        (centralPhysicalVacuumSectorCylinderCauchyToGlobal X)) := by
  let rootSeq := fun stage => CReal.ofQ'
    (centralPhysicalVacuumSectorCylinderOuterRootCoefficientSeq X stage)
  let correctionSeq :=
    centralPhysicalVacuumSectorCylinderOuterHeadCorrectionSeq X
  let centeredRootSeq := fun stage =>
    CReal.add (rootSeq stage) (CReal.neg (correctionSeq stage))
  let oldRootSquareSeq := fun stage => CReal.ofQ'
    (centralPhysicalVacuumSectorCylinderOuterRootCoefficientSeq X stage *
      centralPhysicalVacuumSectorCylinderOuterRootCoefficientSeq X stage)
  let bracketSeq := fun stage =>
    CReal.add
      (CReal.mul (centeredRootSeq stage) (centeredRootSeq stage))
      (CReal.neg (oldRootSquareSeq stage))
  let rootWeightSeq :=
    centralPhysicalVacuumSectorCylinderOuterRootWeightSeq X
  let tailSeq := fun stage =>
    CReal.mul (bracketSeq stage) (rootWeightSeq stage)
  let rawSeq := centralPhysicalVacuumSectorCylinderOuterPulledDiagonalSeq X
  let expansionSeq := fun stage =>
    CReal.add (rawSeq stage) (tailSeq stage)
  let rootLimit :=
    centralPhysicalVacuumSectorCylinderOuterRootCoefficientLimit
      hw0 hw1 half X
  let rawLimit := physicalCauchyPairingLimit hw0 hw1 half
    (centralPhysicalVacuumSectorCylinderCauchyToGlobal X)
    (centralPhysicalVacuumSectorCylinderCauchyToGlobal X)
  let rootWeightLimit :=
    centralPhysicalVacuumSectorCylinderCanonicalRootWeightLimit
      hw0 hw1 half
  have hroot : CReal.ConvergesTo rootSeq rootLimit := by
    simpa only [rootSeq, rootLimit] using
      (centralPhysicalVacuumSectorCylinder_outerRootCoefficient_converges
        hw0 hw1 half X)
  have hcorrection : CReal.ConvergesTo correctionSeq CReal.czero := by
    simpa only [correctionSeq] using
      (centralPhysicalVacuumSectorCylinder_outerHeadCorrection_converges_zero
        hw0 hw1 half X horthogonal)
  have hcenteredRaw := CReal.convergesTo_add hroot
    (CReal.convergesTo_neg hcorrection)
  have hcentered : CReal.ConvergesTo centeredRootSeq rootLimit := by
    apply CReal.convergesTo_limit_congr hcenteredRaw
    exact (CReal.add_congr_right creal_neg_czero).trans
      (creal_add_czero rootLimit)
  have hcenteredSquare :=
    CReal.convergesTo_mul_general hcentered hcentered
  have hrootSquareMul := CReal.convergesTo_mul_general hroot hroot
  have holdRootSquare : CReal.ConvergesTo oldRootSquareSeq
      (CReal.mul rootLimit rootLimit) := by
    apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
      (s := fun stage => CReal.mul (rootSeq stage) (rootSeq stage))
    · intro stage
      exact CReal.Equiv.symm
        (CRealAlg.ofQ'_mul
          (centralPhysicalVacuumSectorCylinderOuterRootCoefficientSeq X stage)
          (centralPhysicalVacuumSectorCylinderOuterRootCoefficientSeq X stage))
    · exact hrootSquareMul
  have hbracketRaw := CReal.convergesTo_add hcenteredSquare
    (CReal.convergesTo_neg holdRootSquare)
  have hbracket : CReal.ConvergesTo bracketSeq CReal.czero := by
    apply CReal.convergesTo_limit_congr hbracketRaw
    exact creal_add_neg_self (CReal.mul rootLimit rootLimit)
  have hrootWeight : CReal.ConvergesTo rootWeightSeq rootWeightLimit := by
    simpa only [rootWeightSeq, rootWeightLimit] using
      (centralPhysicalVacuumSectorCylinder_outerRootWeight_converges
        hw0 hw1 half X)
  have htailRaw := CReal.convergesTo_mul_general hbracket hrootWeight
  have htail : CReal.ConvergesTo tailSeq CReal.czero := by
    apply CReal.convergesTo_limit_congr htailRaw
    exact creal_zero_mul rootWeightLimit
  have hraw : CReal.ConvergesTo rawSeq rawLimit := by
    simpa only [rawSeq, rawLimit] using
      (centralPhysicalVacuumSectorCylinder_outerPulledDiagonal_converges
        hw0 hw1 half X)
  have hexpansionRaw := CReal.convergesTo_add hraw htail
  have hexpansion : CReal.ConvergesTo expansionSeq rawLimit := by
    apply CReal.convergesTo_limit_congr hexpansionRaw
    exact creal_add_czero rawLimit
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (s := expansionSeq)
  · intro stage
    exact CReal.Equiv.symm
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonal_equiv_expansion
        hw0 hw1 (X.seq stage).base half (X.seq stage).coefficient)
  · exact hexpansion

/-- The target of outer centered-diagonal convergence represents the actual
completed squared norm of the quotient class. -/
theorem centralPhysicalVacuumSectorCylinder_completedInner_mk_eq_outerCenteredDiagonalLimit
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
          (centralPhysicalVacuumSectorCylinderCauchyToGlobal X)) :=
  centralPhysicalVacuumSectorCylinder_completedInner_mk_eq_outerRawDiagonalLimit
    hw0 hw1 half X

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterCenteredDiagonal

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterCenteredDiagonal.centralPhysicalVacuumSectorCylinder_rootWeight_equiv_canonical
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterCenteredDiagonal.centralPhysicalVacuumSectorCylinder_outerRootWeight_converges
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterCenteredDiagonal.centralPhysicalVacuumSectorCylinder_outerHeadCenteredDiagonal_converges
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterCenteredDiagonal.centralPhysicalVacuumSectorCylinder_completedInner_mk_eq_outerCenteredDiagonalLimit
