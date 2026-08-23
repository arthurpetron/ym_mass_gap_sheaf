/-
# Vanishing of the BF4 moving sector head correction on dense vacuum vectors

For a dense root-sector cylinder in the actual completed global-vacuum
complement, the preceding pairing theorem identifies its pulled mean limit
with zero.  The denominator of the rational head correction is the pulled
vacuum-root weight, which has one fixed positive rational floor at all
sufficiently large cutoffs.  Dividing the vanishing numerator by this
uniformly positive denominator therefore still converges to zero.

This closes the scalar head-correction edge for dense orthogonal sector
vectors.  It does not yet prove completed-norm convergence of the moving
head-centered presentations, density for arbitrary completed sector vectors,
a carrier-independent strict rate, or any thermodynamic/continuum claim.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseVacuumPairing
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseHeadCorrectionVanishing

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffUniformRowFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseVacuumPairing
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector

local infix:50 " ≈ " => Q'.eqv

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

/-- If a dense root-sector cylinder represents an actual completed vector
orthogonal to the global vacuum, its moving rational head-correction Bishop
real is constructively zero. -/
theorem centralPhysicalVacuumSectorCylinder_headCorrection_equiv_zero_of_orthogonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half)
    (horthogonal : CentralPhysicalVacuumSectorCylinderGlobalVacuumOrthogonal
      hw0 hw1 half
      ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
        hw0 hw1 half).embedRep presentation)) :
    CReal.Equiv
      (centralPhysicalFinitePulledVacuumSectorHeadCorrectionCutoffLimit
        hw0 hw1 presentation.base half presentation.coefficient)
      CReal.czero := by
  let mean :=
    centralPhysicalFinitePulledVacuumSectorWeightedMeanCutoffLimit
      hw0 hw1 presentation.base half presentation.coefficient
  let correction :=
    centralPhysicalFinitePulledVacuumSectorHeadCorrectionCutoffLimit
      hw0 hw1 presentation.base half presentation.coefficient
  let floor := centralPhysicalUniformPositiveRowFloor
    w (Q'.le_of_lt hw0) half
  have hfloor : (0 : Q') < floor :=
    centralPhysicalUniformPositiveRowFloor_pos
      w (Q'.le_of_lt hw0) half
  have hmean : CReal.Equiv mean CReal.czero :=
    centralPhysicalVacuumSectorCylinder_pulledMean_equiv_zero_of_orthogonal
      hw0 hw1 half presentation horthogonal
  intro epsilon hepsilon
  let tolerance := epsilon * floor
  have htolerance : (0 : Q') < tolerance :=
    Q'.mul_pos hepsilon hfloor
  obtain ⟨meanCutoff, hmeanCutoff⟩ := hmean tolerance htolerance
  refine ⟨max meanCutoff
    (centralPhysicalUniformRowFloorCutoff w half), ?_⟩
  intro later hlater
  have hmeanLater := hmeanCutoff later
    (Nat.le_trans (Nat.le_max_left _ _) hlater)
  have hfloorLater :
      centralPhysicalUniformRowFloorCutoff w half ≤ later :=
    Nat.le_trans (Nat.le_max_right _ _) hlater
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
  have hscaled : tolerance ≤ epsilon * denominator := by
    exact Q'.mul_le_mul_of_nonneg_left floor denominator epsilon
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

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseHeadCorrectionVanishing

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseHeadCorrectionVanishing.centralPhysicalVacuumSectorCylinder_headCorrection_equiv_zero_of_orthogonal
