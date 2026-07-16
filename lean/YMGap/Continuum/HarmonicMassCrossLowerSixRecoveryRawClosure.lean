/-
# Raw-sign closure for the lower-six recovery traversal

The energy and one-crossing coordinates naturally prove nonnegativity of the
raw rational drops.  The traversal was deliberately formulated with the
denominator-cleared polynomial signs.  This module proves the constructive
converse transports through the exact positive clearing factors and exposes
the complete all-scale harmonic consequences directly from raw signs.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryTraversalClosure

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryRawClosure

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicGNSMarginRecursion
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryClearing
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryFiniteDifference
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryTraversalClosure
open YMGap.Continuum.HarmonicMassCrossPascalReduction
open YMGap.Continuum.HarmonicMassCrossResidualSandwich
open YMGap.Continuum.HarmonicPolymerBudgetBridge
open YMGap.Continuum.HarmonicTrueMarginStep
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

/-- Multiplication by the two strictly positive consecutive denominator
powers transports a raw within-cell sign to its cleared polynomial sign. -/
theorem lowerSixWithinCellClearedDrop_nonnegative_of_raw
    (k c : Nat) (hraw : (0 : Q') ≤ lowerSixFixedCenterDrop k c) :
    (0 : Q') ≤ lowerSixWithinCellClearedDrop (k + 2) c := by
  let A := qpow (Q'.ofNat (k + 2))
    (lowerSixCenterClearingExponent c)
  let B := qpow (Q'.ofNat (k + 3))
    (lowerSixCenterClearingExponent c)
  have hA : (0 : Q') < A :=
    recovery_clearing_factor_pos (k + 2) _ (by omega)
  have hB : (0 : Q') < B :=
    recovery_clearing_factor_pos (k + 3) _ (by omega)
  have hmul : (0 : Q') ≤ (A * B) * lowerSixFixedCenterDrop k c :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (Q'.le_of_lt hA) (Q'.le_of_lt hB)) hraw
  have hscale := lowerSixFixedCenterDrop_cleared k c
  change (A * B) * lowerSixFixedCenterDrop k c ≈
    lowerSixWithinCellClearedDrop (k + 2) c at hscale
  exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hscale)

/-- Raw-to-cleared transport for the even-to-odd endpoint family. -/
theorem lowerSixEvenOddEndpointClearedDrop_nonnegative_of_raw
    (m : Nat) (hm : 1 ≤ m)
    (hraw : (0 : Q') ≤ lowerSixEvenOddEndpointDrop m) :
    (0 : Q') ≤ lowerSixEvenOddEndpointClearedDrop m := by
  let De := lowerSixEvenCenterRightDen m
  let Do := lowerSixOddCenterRightDen m
  let A := qpow (Q'.ofNat De)
    (lowerSixCenterClearingExponent (2 * m))
  let B := qpow (Q'.ofNat Do)
    (lowerSixCenterClearingExponent (2 * m + 1))
  have hDe : 0 < De := by
    dsimp only [De]
    unfold lowerSixEvenCenterRightDen
    omega
  have hDo : 0 < Do := by
    dsimp only [Do]
    unfold lowerSixOddCenterRightDen
    omega
  have hA : (0 : Q') < A := recovery_clearing_factor_pos De _ hDe
  have hB : (0 : Q') < B := recovery_clearing_factor_pos Do _ hDo
  have hmul : (0 : Q') ≤ (A * B) * lowerSixEvenOddEndpointDrop m :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (Q'.le_of_lt hA) (Q'.le_of_lt hB)) hraw
  have hscale := lowerSixEvenOddEndpointDrop_cleared m hm
  change (A * B) * lowerSixEvenOddEndpointDrop m ≈
    lowerSixEvenOddEndpointClearedDrop m at hscale
  exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hscale)

/-- Raw-to-cleared transport for the odd-to-next-even endpoint family. -/
theorem lowerSixOddEvenEndpointClearedDrop_nonnegative_of_raw
    (m : Nat) (hm : 1 ≤ m)
    (hraw : (0 : Q') ≤ lowerSixOddEvenEndpointDrop m) :
    (0 : Q') ≤ lowerSixOddEvenEndpointClearedDrop m := by
  let Do := lowerSixOddCenterRightDen m
  let De := lowerSixEvenCenterRightDen (m + 1)
  let A := qpow (Q'.ofNat Do)
    (lowerSixCenterClearingExponent (2 * m + 1))
  let B := qpow (Q'.ofNat De)
    (lowerSixCenterClearingExponent (2 * (m + 1)))
  have hDo : 0 < Do := by
    dsimp only [Do]
    unfold lowerSixOddCenterRightDen
    omega
  have hDe : 0 < De := by
    dsimp only [De]
    unfold lowerSixEvenCenterRightDen
    omega
  have hA : (0 : Q') < A := recovery_clearing_factor_pos Do _ hDo
  have hB : (0 : Q') < B := recovery_clearing_factor_pos De _ hDe
  have hmul : (0 : Q') ≤ (A * B) * lowerSixOddEvenEndpointDrop m :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (Q'.le_of_lt hA) (Q'.le_of_lt hB)) hraw
  have hscale := lowerSixOddEvenEndpointDrop_cleared m hm
  change (A * B) * lowerSixOddEvenEndpointDrop m ≈
    lowerSixOddEvenEndpointClearedDrop m at hscale
  exact Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hscale)

/-- Raw within-cell and endpoint signs imply the lower-six residual at every
scale.  This is the direct consumer for the energy/one-crossing route. -/
theorem growingResidualLowerSix_all_of_raw
    (hWithin : ∀ k c : Nat, LowerSixWithinCenterCell (k + 2) c →
      (0 : Q') ≤ lowerSixFixedCenterDrop k c)
    (hEvenOdd : ∀ m : Nat, 5 ≤ m →
      (0 : Q') ≤ lowerSixEvenOddEndpointDrop m)
    (hOddEven : ∀ m : Nat, 5 ≤ m →
      (0 : Q') ≤ lowerSixOddEvenEndpointDrop m) :
    ∀ k : Nat, 10 ≤ k → GrowingResidualLowerSix k := by
  apply growingResidualLowerSix_all_of_cleared
  · intro D c hcell
    have hD2 : 2 ≤ D := hcell.1
    let k := D - 2
    have hkD : k + 2 = D := by dsimp only [k]; omega
    rw [← hkD] at hcell ⊢
    exact lowerSixWithinCellClearedDrop_nonnegative_of_raw k c
      (hWithin k c hcell)
  · intro m hm
    exact lowerSixEvenOddEndpointClearedDrop_nonnegative_of_raw m (by omega)
      (hEvenOdd m hm)
  · intro m hm
    exact lowerSixOddEvenEndpointClearedDrop_nonnegative_of_raw m (by omega)
      (hOddEven m hm)

/-- All-scale physical Pascal cross from the raw sign families. -/
theorem physicalPascalCrossResidual_all_of_raw
    (hWithin : ∀ k c : Nat, LowerSixWithinCenterCell (k + 2) c →
      (0 : Q') ≤ lowerSixFixedCenterDrop k c)
    (hEvenOdd : ∀ m : Nat, 5 ≤ m →
      (0 : Q') ≤ lowerSixEvenOddEndpointDrop m)
    (hOddEven : ∀ m : Nat, 5 ≤ m →
      (0 : Q') ≤ lowerSixOddEvenEndpointDrop m) :
    ∀ k : Nat, PhysicalPascalCrossResidual k :=
  physicalPascalCrossResidual_all_of_growing_lower_six
    (growingResidualLowerSix_all_of_raw hWithin hEvenOdd hOddEven)

/-- Exact coefficient-two harmonic mass-cross bound from raw signs. -/
theorem harmonicMassCross_le_two_invSq_all_of_raw
    (hWithin : ∀ k c : Nat, LowerSixWithinCenterCell (k + 2) c →
      (0 : Q') ≤ lowerSixFixedCenterDrop k c)
    (hEvenOdd : ∀ m : Nat, 5 ≤ m →
      (0 : Q') ≤ lowerSixEvenOddEndpointDrop m)
    (hOddEven : ∀ m : Nat, 5 ≤ m →
      (0 : Q') ≤ lowerSixOddEvenEndpointDrop m)
    (k : Nat) :
    harmonicMassCross k ≤
      (Q'.ofNat 2 * invSqTerm 2 (by decide) k) *
        (harmonicD k * harmonicD (k + 1)) :=
  harmonicMassCross_le_two_invSq_of_physicalPascalCross k
    (physicalPascalCrossResidual_all_of_raw
      hWithin hEvenOdd hOddEven k)

/-- Every adjacent harmonic character-GNS margin step from raw signs. -/
theorem harmonicGNSMargin_singleStep_all_of_raw
    (hWithin : ∀ k c : Nat, LowerSixWithinCenterCell (k + 2) c →
      (0 : Q') ≤ lowerSixFixedCenterDrop k c)
    (hEvenOdd : ∀ m : Nat, 5 ≤ m →
      (0 : Q') ≤ lowerSixEvenOddEndpointDrop m)
    (hOddEven : ∀ m : Nat, 5 ≤ m →
      (0 : Q') ≤ lowerSixOddEvenEndpointDrop m)
    (k : Nat) :
    ((1 : Q') - BondMovingQuadratic.bondMovingDeltaRen 1
        UniformCouplingFromAF.pMult
          (HarmonicCutoffBoundary.harmW k)) *
        harmonicGNSMargin k ≤ harmonicGNSMargin (k + 1) :=
  harmonicGNSMargin_singleStep_of_cross
    (harmonicMassCross_le_two_invSq_all_of_raw
      hWithin hEvenOdd hOddEven) k

/-- Positive all-scale floor for the established harmonic character-GNS
margin from the three raw sign families. -/
theorem harmonicGNS_multiscale_floor_all_of_raw
    (hWithin : ∀ k c : Nat, LowerSixWithinCenterCell (k + 2) c →
      (0 : Q') ≤ lowerSixFixedCenterDrop k c)
    (hEvenOdd : ∀ m : Nat, 5 ≤ m →
      (0 : Q') ≤ lowerSixEvenOddEndpointDrop m)
    (hOddEven : ∀ m : Nat, 5 ≤ m →
      (0 : Q') ≤ lowerSixOddEvenEndpointDrop m) :
    ∀ k : Nat,
      (1 - harmonicModelBudget) * canonicalHarmonicTrueMargin 0 - 0 ≤
          canonicalHarmonicTrueMargin k ∧
        (0 : Q') <
          (1 - harmonicModelBudget) * canonicalHarmonicTrueMargin 0 - 0 :=
  harmonicGNS_multiscale_floor_of_cross
    (harmonicMassCross_le_two_invSq_all_of_raw
      hWithin hEvenOdd hOddEven)

#print axioms lowerSixWithinCellClearedDrop_nonnegative_of_raw
#print axioms lowerSixEvenOddEndpointClearedDrop_nonnegative_of_raw
#print axioms lowerSixOddEvenEndpointClearedDrop_nonnegative_of_raw
#print axioms growingResidualLowerSix_all_of_raw
#print axioms physicalPascalCrossResidual_all_of_raw
#print axioms harmonicMassCross_le_two_invSq_all_of_raw
#print axioms harmonicGNSMargin_singleStep_all_of_raw
#print axioms harmonicGNS_multiscale_floor_all_of_raw

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryRawClosure
