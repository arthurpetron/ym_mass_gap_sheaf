/-
# Outer head-correction vanishing for arbitrary completed BF4 sector vectors

For an arbitrary Cauchy representative of a completed root-sector vector,
the pulled mean limits of its dense terms converge to the completed pairing
with the global vacuum.  If the represented vector is vacuum orthogonal, that
outer mean limit is zero.  The fixed positive pulled-root floor then shows
that the outer sequence of full head-correction Bishop reals converges to
zero as well.

This is the first non-dense component of the completed centered-form
cofinality frontier.  It does not yet prove convergence of the outer centered
diagonal or matrix form sequences, nor any common strict rate or continuum
claim.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Constructive.TrigAddCReal
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedCenteredFormCofinality

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterHeadCorrectionVanishing

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffUniformRowFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Outer sequences attached to one sector representative -/

def centralPhysicalVacuumSectorCylinderOuterPulledMeanSeq
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) (stage : Nat) : CReal :=
  centralPhysicalFinitePulledVacuumSectorWeightedMeanCutoffLimit
    hw0 hw1 (X.seq stage).base half (X.seq stage).coefficient

def centralPhysicalVacuumSectorCylinderOuterHeadCorrectionSeq
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) (stage : Nat) : CReal :=
  centralPhysicalFinitePulledVacuumSectorHeadCorrectionCutoffLimit
    hw0 hw1 (X.seq stage).base half (X.seq stage).coefficient

private theorem sectorCompleted_orthogonal_pairing_equiv_zero
    {w : Q'} {hw0 : (0 : Q') < w} {hw1 : w < (1 : Q')}
    {half : Nat}
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (horthogonal : CentralPhysicalVacuumSectorCylinderGlobalVacuumOrthogonal
      hw0 hw1 half
      (Quotient.mk
        (centralPhysicalVacuumSectorCylinderSquaredSeminorm
          hw0 hw1 half).completionSetoid X)) :
    CReal.Equiv
      (physicalCauchyPairingLimit hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCauchyToGlobal X)
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant centralPhysicalLinearVacuum))
      CReal.czero := by
  unfold CentralPhysicalVacuumSectorCylinderGlobalVacuumOrthogonal
    CentralPhysicalCutoffCompletedVacuumOrthogonal
    centralPhysicalCutoffCompletedVacuum
    embedCentralPhysicalLinearObservable at horthogonal
  change Quotient.mk CReal.crealSetoid
      (physicalCauchyPairingLimit hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCauchyToGlobal X)
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant centralPhysicalLinearVacuum)) =
    CReal.RCzero at horthogonal
  exact Quotient.exact horthogonal

/-- The pulled mean limits of the dense terms of any sector representative
converge to the representative's actual completed vacuum pairing. -/
theorem centralPhysicalVacuumSectorCylinder_outerPulledMean_converges_pairing
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    CReal.ConvergesTo
      (centralPhysicalVacuumSectorCylinderOuterPulledMeanSeq X)
      (physicalCauchyPairingLimit hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCauchyToGlobal X)
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant centralPhysicalLinearVacuum)) := by
  apply YMGap.Constructive.TrigAddCReal.convergesTo_congr_seq
    (s := physicalCauchyPairingSeq hw0 hw1 half
      (centralPhysicalVacuumSectorCylinderCauchyToGlobal X)
      ((centralPhysicalCutoffLinearSquaredSeminorm
        hw0 hw1 half).constant centralPhysicalLinearVacuum))
  · intro stage
    change CReal.Equiv
      (innerLimit hw0 hw1 half
        (X.seq stage).toLinearObservable centralPhysicalLinearVacuum)
      (centralPhysicalFinitePulledVacuumSectorWeightedMeanCutoffLimit
        hw0 hw1 (X.seq stage).base half (X.seq stage).coefficient)
    exact
      YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseVacuumPairing.centralPhysicalVacuumSectorCylinder_innerLimitVacuum_equiv_pulledMean
        hw0 hw1 half (X.seq stage)
  · exact physicalCauchyPairingSeq_converges hw0 hw1 half
      (centralPhysicalVacuumSectorCylinderCauchyToGlobal X)
      ((centralPhysicalCutoffLinearSquaredSeminorm
        hw0 hw1 half).constant centralPhysicalLinearVacuum)

/-- Completed sector vacuum orthogonality makes the outer pulled-mean
sequence converge to zero. -/
theorem centralPhysicalVacuumSectorCylinder_outerPulledMean_converges_zero
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
      (centralPhysicalVacuumSectorCylinderOuterPulledMeanSeq X)
      CReal.czero :=
  CReal.convergesTo_limit_congr
    (centralPhysicalVacuumSectorCylinder_outerPulledMean_converges_pairing
      hw0 hw1 half X)
    (sectorCompleted_orthogonal_pairing_equiv_zero X horthogonal)

/-! ## 2. Uniform division by the positive pulled root -/

private theorem abs_divPos_le_of_abs_le_mul_local
    {numerator denominator budget : Q'}
    (hdenominator : (0 : Q') < denominator)
    (hcross : Q'.abs numerator ≤ budget * denominator) :
    Q'.abs (Q'.divPos numerator denominator hdenominator) ≤ budget := by
  apply Q'.abs_le
  · apply Q'.le_divPos_of_mul_le
    have hnegCross :
        -(budget * denominator) ≤ -(Q'.abs numerator) :=
      Q'.neg_le_neg hcross
    have hnegAbs : -(Q'.abs numerator) ≤ numerator := by
      have h := Q'.neg_le_neg (Q'.neg_le_abs numerator)
      exact Q'.le_trans' _ _ _ h
        (Q'.le_of_eqv (Q'.neg_neg_eqv numerator))
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.neg_mul_eqv budget denominator))
      (Q'.le_trans' _ _ _ hnegCross hnegAbs)
  · apply Q'.divPos_le_of_le_mul
    exact Q'.le_trans' _ _ _ (Q'.le_abs_self numerator) hcross

private theorem two_sided_zero_add_of_abs_le_local
    {value epsilon : Q'} (h : Q'.abs value ≤ epsilon) :
    value ≤ (0 : Q') + epsilon ∧
      (0 : Q') ≤ value + epsilon := by
  have hzero : value + -(0 : Q') ≈ value :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left value (-(0 : Q')) 0 (by decide))
      (Q'.eqv_of_eq (Q'.add_zero' value))
  have hforward : Q'.abs (value + -(0 : Q')) ≤ epsilon :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr hzero)) h
  exact
    ⟨ExpNeg.le_add_of_abs_sub_le hforward,
      ExpNeg.le_add_of_abs_sub_le
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv
            (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm 0 value))
          hforward)⟩

/-- For any representative of an actual completed sector vacuum vector, the
outer sequence of complete head-correction Bishop reals converges to zero. -/
theorem centralPhysicalVacuumSectorCylinder_outerHeadCorrection_converges_zero
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
      (centralPhysicalVacuumSectorCylinderOuterHeadCorrectionSeq X)
      CReal.czero := by
  let meanSeq := centralPhysicalVacuumSectorCylinderOuterPulledMeanSeq X
  let correctionSeq :=
    centralPhysicalVacuumSectorCylinderOuterHeadCorrectionSeq X
  let floor := centralPhysicalUniformPositiveRowFloor
    w (Q'.le_of_lt hw0) half
  have hfloor : (0 : Q') < floor :=
    centralPhysicalUniformPositiveRowFloor_pos
      w (Q'.le_of_lt hw0) half
  have hmean : CReal.ConvergesTo meanSeq CReal.czero :=
    centralPhysicalVacuumSectorCylinder_outerPulledMean_converges_zero
      hw0 hw1 half X horthogonal
  intro epsilon hepsilon
  let tolerance := epsilon * floor
  have htolerance : (0 : Q') < tolerance :=
    Q'.mul_pos hepsilon hfloor
  obtain ⟨meanStage, hmeanStage⟩ := hmean tolerance htolerance
  refine ⟨meanStage, ?_⟩
  intro stage hstage
  obtain ⟨meanApprox, hmeanApprox⟩ := hmeanStage stage hstage
  refine ⟨max meanApprox
    (centralPhysicalUniformRowFloorCutoff w half), ?_⟩
  intro later hlater
  have hmeanLater := hmeanApprox later
    (Nat.le_trans (Nat.le_max_left _ _) hlater)
  have hfloorLater :
      centralPhysicalUniformRowFloorCutoff w half ≤ later :=
    Nat.le_trans (Nat.le_max_right _ _) hlater
  let presentation := X.seq stage
  let numerator :=
    centralPhysicalFinitePulledVacuumSectorWeightedMean
      w (Q'.le_of_lt hw0) presentation.base later half
        presentation.coefficient
  let denominator := centralPhysicalFinitePulledWeight
    w (Q'.le_of_lt hw0) presentation.base later half 0
  have hdenominator : (0 : Q') < denominator :=
    centralPhysicalFinitePulledWeight_zero_pos
      w (Q'.le_of_lt hw0) presentation.base later half
  have hfloorDenominator : floor ≤ denominator :=
    centralPhysicalUniformPositiveRowFloor_le_pulledWeight_zero
      hw0 hw1 presentation.base half hfloorLater
  change numerator ≤ (0 : Q') + tolerance ∧
    (0 : Q') ≤ numerator + tolerance at hmeanLater
  have hnumeratorRaw :
      Q'.abs (numerator + -(0 : Q')) ≤ tolerance :=
    CReal.abs_sub_le_of_bounds hmeanLater.1 hmeanLater.2
  have hzero : numerator + -(0 : Q') ≈ numerator :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left numerator (-(0 : Q')) 0 (by decide))
      (Q'.eqv_of_eq (Q'.add_zero' numerator))
  have hnumerator : Q'.abs numerator ≤ tolerance :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.eqv_symm hzero)))
      hnumeratorRaw
  have hscaled : tolerance ≤ epsilon * denominator :=
    Q'.mul_le_mul_of_nonneg_left floor denominator epsilon
      hfloorDenominator (Q'.le_of_lt hepsilon)
  have hquotient :
      Q'.abs (Q'.divPos numerator denominator hdenominator) ≤ epsilon :=
    abs_divPos_le_of_abs_le_mul_local hdenominator
      (Q'.le_trans' _ _ _ hnumerator hscaled)
  change Q'.divPos numerator denominator hdenominator ≤
      (0 : Q') + epsilon ∧
    (0 : Q') ≤
      Q'.divPos numerator denominator hdenominator + epsilon
  exact two_sided_zero_add_of_abs_le_local hquotient

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterHeadCorrectionVanishing

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterHeadCorrectionVanishing.centralPhysicalVacuumSectorCylinder_outerPulledMean_converges_pairing
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterHeadCorrectionVanishing.centralPhysicalVacuumSectorCylinder_outerPulledMean_converges_zero
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterHeadCorrectionVanishing.centralPhysicalVacuumSectorCylinder_outerHeadCorrection_converges_zero
