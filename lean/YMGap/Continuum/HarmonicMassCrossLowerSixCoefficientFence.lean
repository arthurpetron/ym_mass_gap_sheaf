/-
The raw Bernstein/Pascal coefficientwise route to the lower-six residual
cannot work: its constant coefficient is exactly `-5` at every supported
head.  Any proof must retain cancellation between Pascal coefficients.
-/

import YMGap.Continuum.HarmonicMassCrossResidualSandwich

namespace YMGap.Continuum.HarmonicMassCrossLowerSixCoefficientFence

set_option maxRecDepth 30000

open YMGap.Continuum
open YMGap.Continuum.HarmonicMovingDeterminantThetaSevenPascalRecurrence
open YMGap.Continuum.HarmonicThetaPascalBridge

def massSixCellCoeff (D n j : Nat) : Int :=
  Int.ofNat (6 * n * n) *
    (thetaMonoBernCoeff D (2 * n * n - 2) j -
      2 * thetaMonoBernCoeff D (2 * n * n - 1) j +
      thetaMonoBernCoeff D (2 * n * n) j)

def massSixHeadCoeff (D j : Nat) : Nat → Int
  | 0 => 0
  | n + 1 => massSixHeadCoeff D j n + massSixCellCoeff D (n + 1) j

def lowerSixCoeff (m j : Nat) : Int :=
  let D := sevenGapDegree m
  growingHeadThetaBernCoeff D m j - massSixHeadCoeff D j (m - 1)

private theorem thetaDiagBernCoeff_one_zero (D : Nat) :
    thetaDiagBernCoeff D 1 0 = 1 := by
  simp [thetaDiagBernCoeff, thetaMonoBernCoeff, PNPaths.choose]

private theorem thetaDiagBernCoeff_zero_of_two_le
    (D n : Nat) (hn : 2 ≤ n) : thetaDiagBernCoeff D n 0 = 0 := by
  have hs : 4 ≤ n * n := Nat.mul_le_mul hn hn
  have ht : 8 ≤ 2 * n * n := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hs
  have h0 : 2 * n * n - 2 ≠ 0 := by omega
  have h1 : 2 * n * n - 1 ≠ 0 := by omega
  have h2 : 2 * n * n ≠ 0 := by omega
  simp [thetaDiagBernCoeff, thetaMonoBernCoeff, h0, h1, h2]

private theorem thetaOffBernCoeff_zero_of_one_le
    (D n : Nat) (hn : 1 ≤ n) : thetaOffBernCoeff D n 0 = 0 := by
  have h2n : 2 ≤ 2 * n := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left 2 hn
  have hp0 := Nat.mul_le_mul h2n (by omega : 1 ≤ n + 1)
  have hp : 2 ≤ 2 * n * (n + 1) := by
    simpa only [Nat.mul_one] using hp0
  have h : 2 * n * (n + 1) - 1 ≠ 0 := by omega
  simp [thetaOffBernCoeff, thetaMonoBernCoeff, h]

private theorem massSixCellCoeff_one_zero (D : Nat) :
    massSixCellCoeff D 1 0 = 6 := by
  simp [massSixCellCoeff, thetaMonoBernCoeff, PNPaths.choose]

private theorem massSixCellCoeff_zero_of_two_le
    (D n : Nat) (hn : 2 ≤ n) : massSixCellCoeff D n 0 = 0 := by
  have hs : 4 ≤ n * n := Nat.mul_le_mul hn hn
  have ht : 8 ≤ 2 * n * n := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hs
  have h0 : 2 * n * n - 2 ≠ 0 := by omega
  have h1 : 2 * n * n - 1 ≠ 0 := by omega
  have h2 : 2 * n * n ≠ 0 := by omega
  simp [massSixCellCoeff, thetaMonoBernCoeff, h0, h1, h2]

theorem massSixHeadCoeff_zero (D c : Nat) (hc : 1 ≤ c) :
    massSixHeadCoeff D 0 c = 6 := by
  induction c with
  | zero => omega
  | succ c ih =>
      cases c with
      | zero =>
          simpa [massSixHeadCoeff] using massSixCellCoeff_one_zero D
      | succ c =>
          rw [massSixHeadCoeff, ih (by omega)]
          have hz := massSixCellCoeff_zero_of_two_le D (c + 1 + 1) (by omega)
          rw [hz]
          omega

theorem cumulativeThetaBernCoeff_zero_of_two_le (D n c : Nat) (hn : 2 ≤ n) :
    cumulativeThetaBernCoeff D n 0 c = 0 := by
  induction c generalizing n with
  | zero =>
      simp only [cumulativeThetaBernCoeff]
      exact thetaDiagBernCoeff_zero_of_two_le D n hn
  | succ c ih =>
      simp only [cumulativeThetaBernCoeff]
      have hd := thetaDiagBernCoeff_zero_of_two_le D n hn
      have ho := thetaOffBernCoeff_zero_of_one_le D n (by omega)
      rw [hd, ho, ih (n + 1) (by omega)]
      omega

theorem cumulativeThetaBernCoeff_one_zero (D c : Nat) :
    cumulativeThetaBernCoeff D 1 0 c = 1 := by
  cases c with
  | zero =>
      simpa only [cumulativeThetaBernCoeff] using thetaDiagBernCoeff_one_zero D
  | succ c =>
      simp only [cumulativeThetaBernCoeff]
      have hd := thetaDiagBernCoeff_one_zero D
      have ho := thetaOffBernCoeff_zero_of_one_le D 1 (by omega)
      rw [hd, ho, cumulativeThetaBernCoeff_zero_of_two_le D 2 c (by omega)]
      omega

theorem growingHeadThetaBernCoeff_zero (m : Nat) (hm : 2 ≤ m) :
    growingHeadThetaBernCoeff (sevenGapDegree m) m 0 = 1 := by
  unfold growingHeadThetaBernCoeff
  rw [cumulativeThetaBernCoeff_one_zero]
  have hz := thetaDiagBernCoeff_zero_of_two_le (sevenGapDegree m) m hm
  rw [hz]
  omega

theorem lowerSixCoeff_zero (m : Nat) (hm : 2 ≤ m) :
    lowerSixCoeff m 0 = -5 := by
  dsimp only [lowerSixCoeff]
  rw [growingHeadThetaBernCoeff_zero m hm,
    massSixHeadCoeff_zero (sevenGapDegree m) (m - 1) (by omega)]
  omega

#print axioms growingHeadThetaBernCoeff_zero
#print axioms lowerSixCoeff_zero

end YMGap.Continuum.HarmonicMassCrossLowerSixCoefficientFence
