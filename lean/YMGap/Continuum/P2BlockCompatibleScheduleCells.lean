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

theorem blockWeight_three_eqv :
    blockWeight 3 ≈ Q'.mkPos 767 768 (by decide) := by decide

theorem blockWeight_four_eqv :
    blockWeight 4 ≈ Q'.mkPos 3071 3072 (by decide) := by decide

def blockScaledModeZero : Q' :=
  scaledModeOne 11 12 (blockNcut 0) (by decide)

def blockScaledModeOne : Q' :=
  scaledModeOne 47 48 (blockNcut 1) (by decide)

def blockScaledModeTwo : Q' :=
  scaledModeOne 191 192 (blockNcut 2) (by decide)

def blockScaledModeThree : Q' :=
  scaledModeOne 767 768 (blockNcut 3) (by decide)

def blockScaledModeFour : Q' :=
  scaledModeOne 3071 3072 (blockNcut 4) (by decide)

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

theorem blockRawModeThree_eqv : blockRawModeOne 3 ≈ blockScaledModeThree :=
  p2VacNorm_one_eqv_scaled 767 768 (by decide) (blockWeight 3)
    blockWeight_three_eqv (blockWeight_nonneg 3) (blockWeight_le_one 3)
    (blockNcut 3) (by decide)

theorem blockRawModeFour_eqv : blockRawModeOne 4 ≈ blockScaledModeFour :=
  p2VacNorm_one_eqv_scaled 3071 3072 (by decide) (blockWeight 4)
    blockWeight_four_eqv (blockWeight_nonneg 4) (blockWeight_le_one 4)
    (blockNcut 4) (by decide)

theorem blockScaled_step_zero :
    blockScaledModeZero <= qpow blockScaledModeOne 2 := by decide

theorem blockScaled_step_one :
    blockScaledModeOne <= qpow blockScaledModeTwo 2 := by decide

theorem blockScaled_step_two :
    blockScaledModeTwo <= qpow blockScaledModeThree 2 := by decide

theorem blockScaled_step_three :
    blockScaledModeThree <= qpow blockScaledModeFour 2 := by decide

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

/-- Third exact physical square cell, the first member of the former
structural tail. -/
theorem blockRaw_step_two :
    blockRawModeOne 2 <= qpow (blockRawModeOne 3) 2 :=
  transport_scaled_square blockRawModeTwo_eqv blockRawModeThree_eqv
    blockScaled_step_two

/-- Fourth exact physical square cell. -/
theorem blockRaw_step_three :
    blockRawModeOne 3 <= qpow (blockRawModeOne 4) 2 :=
  transport_scaled_square blockRawModeThree_eqv blockRawModeFour_eqv
    blockScaled_step_three

end YMGap.Continuum.P2BlockCompatibleScheduleCells

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2BlockCompatibleScheduleCells.blockRaw_step_zero
#print axioms YMGap.Continuum.P2BlockCompatibleScheduleCells.blockRaw_step_one
#print axioms YMGap.Continuum.P2BlockCompatibleScheduleCells.blockRaw_step_two
#print axioms YMGap.Continuum.P2BlockCompatibleScheduleCells.blockRaw_step_three
