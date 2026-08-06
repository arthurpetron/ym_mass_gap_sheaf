/-
Track 11.7-fusion / R3a -- exact initial cells for the block-compatible
physical cutoff schedule.

The common-denominator natural-number evaluator proves the first two genuine
mode-one square cells for `N = 4, 9, 19` and weights
`11/12, 47/48, 191/192`.  Keeping these larger closed computations separate
from the structural schedule kernel makes subsequent all-scale work cheap.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2BlockCompatibleSchedule

namespace YMGap.Continuum.P2BlockCompatibleScheduleCells

set_option maxRecDepth 30000
set_option exponentiation.threshold 10000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingRetuneFix
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2RetunedRatioCompiler
open YMGap.Continuum.P2VacNormIntegralCertificate
open YMGap.Continuum.RGTransport
open YMGap.Continuum.VacNormEigShift

local infix:50 " ≈ " => Q'.eqv

/-- Raw physical mode one on the block-compatible schedule. -/
def blockRawModeOne (k : Nat) : Q' :=
  p2VacNorm (blockNcut k) (blockWeight_nonneg k) (blockWeight_le_one k) 1

theorem blockWeight_zero_eqv :
    blockWeight 0 ≈ Q'.mkPos 11 12 (by decide) := by decide

theorem blockWeight_one_eqv :
    blockWeight 1 ≈ Q'.mkPos 47 48 (by decide) := by decide

theorem blockWeight_two_eqv :
    blockWeight 2 ≈ Q'.mkPos 191 192 (by decide) := by decide

def blockScaledModeZero : Q' :=
  scaledModeOne 11 12 (blockNcut 0) (by decide)

def blockScaledModeOne : Q' :=
  scaledModeOne 47 48 (blockNcut 1) (by decide)

def blockScaledModeTwo : Q' :=
  scaledModeOne 191 192 (blockNcut 2) (by decide)

theorem blockRawModeZero_eqv : blockRawModeOne 0 ≈ blockScaledModeZero :=
  p2VacNorm_one_eqv_scaled 11 12 (by decide) (blockWeight 0)
    blockWeight_zero_eqv (blockWeight_nonneg 0) (blockWeight_le_one 0)
    (blockNcut 0) (by decide)

theorem blockRawModeOne_eqv : blockRawModeOne 1 ≈ blockScaledModeOne :=
  p2VacNorm_one_eqv_scaled 47 48 (by decide) (blockWeight 1)
    blockWeight_one_eqv (blockWeight_nonneg 1) (blockWeight_le_one 1)
    (blockNcut 1) (by decide)

theorem blockRawModeTwo_eqv : blockRawModeOne 2 ≈ blockScaledModeTwo :=
  p2VacNorm_one_eqv_scaled 191 192 (by decide) (blockWeight 2)
    blockWeight_two_eqv (blockWeight_nonneg 2) (blockWeight_le_one 2)
    (blockNcut 2) (by decide)

theorem blockScaled_step_zero :
    blockScaledModeZero <= qpow blockScaledModeOne 2 := by decide

theorem blockScaled_step_one :
    blockScaledModeOne <= qpow blockScaledModeTwo 2 := by decide

private theorem transport_scaled_square {rawCoarse rawFine scaledCoarse scaledFine : Q'}
    (hc : rawCoarse ≈ scaledCoarse) (hf : rawFine ≈ scaledFine)
    (hscaled : scaledCoarse <= qpow scaledFine 2) :
    rawCoarse <= qpow rawFine 2 := by
  have hpow := BondMovingRelResidual.qpow_eqv_congr_base hf 2
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hc)
    (Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv hpow))

/-- First exact physical square cell on the replacement schedule. -/
theorem blockRaw_step_zero :
    blockRawModeOne 0 <= qpow (blockRawModeOne 1) 2 :=
  transport_scaled_square blockRawModeZero_eqv blockRawModeOne_eqv
    blockScaled_step_zero

/-- Second exact physical square cell on the replacement schedule. -/
theorem blockRaw_step_one :
    blockRawModeOne 1 <= qpow (blockRawModeOne 2) 2 :=
  transport_scaled_square blockRawModeOne_eqv blockRawModeTwo_eqv
    blockScaled_step_one

end YMGap.Continuum.P2BlockCompatibleScheduleCells

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2BlockCompatibleScheduleCells.blockRaw_step_zero
#print axioms YMGap.Continuum.P2BlockCompatibleScheduleCells.blockRaw_step_one
