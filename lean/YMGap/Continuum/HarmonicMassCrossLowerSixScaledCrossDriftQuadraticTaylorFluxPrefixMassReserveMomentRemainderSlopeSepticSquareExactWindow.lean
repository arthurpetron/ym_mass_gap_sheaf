/-
Mode-sensitive septic square enclosures on the physical prefix.

The uniform inverse-cube width is useful for coarse estimates, but paying it
independently at every mode destroys the finite-Hermite cross-scale
cancellation.  Here the generic sign-agnostic square lemmas retain the exact
seventh-order, mode-dependent error instead.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticLowerFence

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticSquareExactWindow

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSeptic
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticSquare
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticSquareWindow
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticWindow
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftSuffix
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow

private theorem thetaWindowLeft_mono_step (k : Nat) :
    thetaWindowLeft k ≤ thetaWindowLeft (k + 1) := by
  have h := thetaWindowCenter_mono_step k
  unfold thetaWindowLeft
  omega

private theorem invDenCube_le_one (k : Nat) :
    Q'.mkPos 1 ((k + 2) * ((k + 2) * (k + 2)))
        (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))) ≤
      (1 : Q') := by
  let T : Q' := Q'.mkPos 1 ((k + 2) * ((k + 2) * (k + 2)))
    (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega)))
  change T ≤ (1 : Q')
  change T.num * ((1 : Q').den : Int) ≤
    (1 : Q').num * (T.den : Int)
  dsimp only [T]
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d]
  simp only [Q'.mkPos_num, Q'.mkPos_den, Int.mul_one, Int.one_mul]
  have hD : 1 ≤ k + 2 := by omega
  have hcube : 1 ≤ (k + 2) * ((k + 2) * (k + 2)) :=
    Nat.mul_le_mul hD (Nat.mul_le_mul hD hD)
  exact_mod_cast hcube

/-- The exact mode-sensitive seventh-order error is at most one. -/
theorem lowerSixRootSlopeTaylor6Error_le_one_large
    {k n : Nat} (hk : 390 ≤ k) (hn : n ≤ thetaWindowLeft k) :
    rootSlopeTaylor6Error (harmU k) n ≤ (1 : Q') := by
  exact Q'.le_trans' _ _ _
    (lowerSixRootSlopeTaylor6Error_le_invDenCube_large hk hn)
    (invDenCube_le_one k)

/-- Old-slope square upper bound retaining the exact mode-sensitive error. -/
theorem lowerSixThetaRootSlope_square_le_Taylor6_square_add_three_exactError
    {k n : Nat} (hk : 390 ≤ k) (hn : n ≤ thetaWindowLeft k) :
    thetaRootSlope k n * thetaRootSlope k n ≤
      rootSlopeTaylor6 (harmU k) n * rootSlopeTaylor6 (harmU k) n +
        Q'.ofNat 3 * rootSlopeTaylor6Error (harmU k) n := by
  exact square_le_model_square_add_three_error
    (lowerSixThetaRootSlopeTaylor6_le k n)
    (lowerSixThetaRootSlope_le_Taylor6_add_error k n)
    (lowerSixThetaRootSlope_le_one_large hk hn)
    (lowerSixRootSlopeTaylor6Error_le_one_large hk hn)

/-- Next-slope square lower bound retaining the exact mode-sensitive error. -/
theorem lowerSixTaylor6Next_square_sub_four_exactError_le_ThetaRootSlope_square
    {k n : Nat} (hk : 390 ≤ k) (hn : n ≤ thetaWindowLeft k) :
    rootSlopeTaylor6 (harmU (k + 1)) n *
          rootSlopeTaylor6 (harmU (k + 1)) n +
        -(Q'.ofNat 4 * rootSlopeTaylor6Error (harmU (k + 1)) n) ≤
      thetaRootSlope (k + 1) n * thetaRootSlope (k + 1) n := by
  have hnnext : n ≤ thetaWindowLeft (k + 1) :=
    Nat.le_trans hn (thetaWindowLeft_mono_step k)
  exact model_square_sub_four_error_le_square
    (lowerSixThetaRootSlope_ge_neg_one (k + 1) n)
    (lowerSixThetaRootSlopeTaylor6_le (k + 1) n)
    (lowerSixThetaRootSlope_le_Taylor6_add_error (k + 1) n)
    (lowerSixRootSlopeTaylor6Error_le_one_large (by omega) hnnext)

#print axioms lowerSixRootSlopeTaylor6Error_le_one_large
#print axioms lowerSixThetaRootSlope_square_le_Taylor6_square_add_three_exactError
#print axioms lowerSixTaylor6Next_square_sub_four_exactError_le_ThetaRootSlope_square

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticSquareExactWindow
