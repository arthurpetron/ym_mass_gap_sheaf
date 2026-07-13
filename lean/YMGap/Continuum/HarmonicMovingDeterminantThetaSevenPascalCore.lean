/-
Exact Bernstein row for the seven-Dirichlet core payment.

The seven-unit gap row still contains the positive terminal integer mode.
After the common `w^2` factor has been removed, that endpoint is the single
monomial `4m^2 w^(2m^2-2)`.  Removing it changes only deficits zero through
three at the minimal degree.  In particular, every bulk theorem beginning at
deficit four transfers unchanged to the exact core row.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalRecurrence

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalCore

open YMGap.Continuum
open YMGap.Continuum.HarmonicThetaPascalBridge
open YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalRow
open YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalRecurrence

/-- Exact coefficient row of the seven-Dirichlet core after removing the
positive terminal endpoint from the seven-unit gap row. -/
def sevenCoreBernCoeff (D m j : Nat) : Int :=
  sevenGapBernCoeff D m j -
    Int.ofNat (4 * m * m) * thetaMonoBernCoeff D (2 * m * m - 2) j

/-- Minimal core row in deficit coordinates, extended by zero. -/
def sevenCoreDeficit (m r : Nat) : Int :=
  if r ≤ sevenGapDegree m then
    sevenCoreBernCoeff (sevenGapDegree m) m (sevenGapDegree m - r)
  else 0

private theorem square_pos {m : Nat} (hm : 1 ≤ m) : 1 ≤ m * m := by
  simpa only [Nat.one_mul] using Nat.mul_le_mul hm hm

private theorem double_square_two {m : Nat} (hm : 1 ≤ m) :
    2 ≤ 2 * m * m := by
  have hs := square_pos hm
  simpa only [Nat.mul_assoc, Nat.mul_one] using Nat.mul_le_mul_left 2 hs

private theorem endpoint_mono_zero (m : Nat) (hm : 1 ≤ m) :
    thetaMonoBernCoeff (2 * m * m + 1) (2 * m * m - 2)
      (2 * m * m + 1) = 1 := by
  have hA := double_square_two hm
  unfold thetaMonoBernCoeff
  rw [if_pos (by omega)]
  have htop : 2 * m * m + 1 - (2 * m * m - 2) = 3 := by omega
  rw [htop]
  decide

private theorem endpoint_mono_one (m : Nat) (hm : 1 ≤ m) :
    thetaMonoBernCoeff (2 * m * m + 1) (2 * m * m - 2)
      (2 * m * m + 1 - 1) = 3 := by
  have hA := double_square_two hm
  unfold thetaMonoBernCoeff
  rw [if_pos (by omega)]
  have htop : 2 * m * m + 1 - (2 * m * m - 2) = 3 := by omega
  have hidx : 2 * m * m + 1 - 1 - (2 * m * m - 2) = 2 := by omega
  rw [htop, hidx]
  decide

private theorem endpoint_mono_two (m : Nat) (hm : 1 ≤ m) :
    thetaMonoBernCoeff (2 * m * m + 1) (2 * m * m - 2)
      (2 * m * m + 1 - 2) = 3 := by
  have hA := double_square_two hm
  unfold thetaMonoBernCoeff
  rw [if_pos (by omega)]
  have htop : 2 * m * m + 1 - (2 * m * m - 2) = 3 := by omega
  have hidx : 2 * m * m + 1 - 2 - (2 * m * m - 2) = 1 := by omega
  rw [htop, hidx]
  decide

private theorem endpoint_mono_three (m : Nat) (hm : 1 ≤ m) :
    thetaMonoBernCoeff (2 * m * m + 1) (2 * m * m - 2)
      (2 * m * m + 1 - 3) = 1 := by
  have hA := double_square_two hm
  unfold thetaMonoBernCoeff
  rw [if_pos (by omega)]
  have htop : 2 * m * m + 1 - (2 * m * m - 2) = 3 := by omega
  have hidx : 2 * m * m + 1 - 3 - (2 * m * m - 2) = 0 := by omega
  rw [htop, hidx]
  decide

/-- At the minimal degree, the removed endpoint has no coefficient from
deficit four onward. -/
theorem sevenCoreDeficit_eq_sevenGapDeficit_of_four_le
    (m r : Nat) (hm : 1 ≤ m) (hr : 4 ≤ r) :
    sevenCoreDeficit m r = sevenGapDeficit m r := by
  unfold sevenCoreDeficit sevenGapDeficit
  by_cases hrD : r ≤ sevenGapDegree m
  · rw [if_pos hrD, if_pos hrD]
    unfold sevenCoreBernCoeff
    have hA := double_square_two hm
    have hrD' : r ≤ 2 * m * m + 1 := by
      simpa only [sevenGapDegree] using hrD
    have hnot : ¬ 2 * m * m - 2 ≤ (2 * m * m + 1) - r := by
      omega
    change sevenGapBernCoeff (sevenGapDegree m) m (sevenGapDegree m - r) -
      Int.ofNat (4 * m * m) *
        thetaMonoBernCoeff (sevenGapDegree m) (2 * m * m - 2)
          (sevenGapDegree m - r) =
      sevenGapBernCoeff (sevenGapDegree m) m (sevenGapDegree m - r)
    simp only [sevenGapDegree, thetaMonoBernCoeff, if_neg hnot,
      Int.mul_zero, Int.sub_zero]
  · rw [if_neg hrD, if_neg hrD]

/-- Core correction at top deficit zero: subtract `4m^2`. -/
theorem sevenCoreDeficit_zero (m : Nat) (hm : 1 ≤ m) :
    sevenCoreDeficit m 0 = sevenGapDeficit m 0 - Int.ofNat (4 * m * m) := by
  unfold sevenCoreDeficit sevenGapDeficit sevenCoreBernCoeff sevenGapDegree
  simp only [Nat.zero_le, if_pos, Nat.sub_zero]
  rw [endpoint_mono_zero m hm]
  omega

/-- Core correction at deficit one: subtract `12m^2`. -/
theorem sevenCoreDeficit_one (m : Nat) (hm : 1 ≤ m) :
    sevenCoreDeficit m 1 =
      sevenGapDeficit m 1 - 3 * Int.ofNat (4 * m * m) := by
  have hA := double_square_two hm
  have hD : 1 ≤ 2 * m * m + 1 := by omega
  unfold sevenCoreDeficit sevenGapDeficit sevenCoreBernCoeff sevenGapDegree
  rw [if_pos hD, if_pos hD]
  rw [endpoint_mono_one m hm]
  omega

/-- Core correction at deficit two: subtract `12m^2`. -/
theorem sevenCoreDeficit_two (m : Nat) (hm : 1 ≤ m) :
    sevenCoreDeficit m 2 =
      sevenGapDeficit m 2 - 3 * Int.ofNat (4 * m * m) := by
  have hA := double_square_two hm
  have hD : 2 ≤ 2 * m * m + 1 := by omega
  unfold sevenCoreDeficit sevenGapDeficit sevenCoreBernCoeff sevenGapDegree
  rw [if_pos hD, if_pos hD]
  rw [endpoint_mono_two m hm]
  omega

/-- Core correction at deficit three: subtract `4m^2`. -/
theorem sevenCoreDeficit_three (m : Nat) (hm : 1 ≤ m) :
    sevenCoreDeficit m 3 =
      sevenGapDeficit m 3 - Int.ofNat (4 * m * m) := by
  have hA := double_square_two hm
  have hD : 3 ≤ 2 * m * m + 1 := by omega
  unfold sevenCoreDeficit sevenGapDeficit sevenCoreBernCoeff sevenGapDegree
  rw [if_pos hD, if_pos hD]
  rw [endpoint_mono_three m hm]
  simp only [Int.mul_one]

#print axioms sevenCoreBernCoeff
#print axioms sevenCoreDeficit
#print axioms sevenCoreDeficit_eq_sevenGapDeficit_of_four_le
#print axioms sevenCoreDeficit_zero
#print axioms sevenCoreDeficit_one
#print axioms sevenCoreDeficit_two
#print axioms sevenCoreDeficit_three

end YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalCore
