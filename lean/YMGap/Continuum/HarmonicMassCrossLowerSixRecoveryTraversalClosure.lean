/-
# All-scale closure from the three lower-six cleared sign families

The finite-cell traversal isolates three analytic polynomial signs.  This
module records their exact downstream force without weakening them or hiding
them in a new frontier carrier: together they close the lower-six residual at
every scale, the physical Pascal cross, the coefficient-two harmonic mass
cross, and the established character-GNS multiscale margin floor.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryTraversal
import YMGap.Continuum.HarmonicLowerSixTailEnvelopeProductionAnchorClosure

namespace YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryTraversalClosure

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicGNSMarginRecursion
open YMGap.Continuum.HarmonicLowerSixTailEnvelopeProductionAnchorClosure
open YMGap.Continuum.HarmonicMassCrossLowerSixDirichlet
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryClearing
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryFiniteDifference
open YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryTraversal
open YMGap.Continuum.HarmonicMassCrossPascalReduction
open YMGap.Continuum.HarmonicMassCrossResidualSandwich
open YMGap.Continuum.HarmonicPolymerBudgetBridge
open YMGap.Continuum.HarmonicTrueMarginStep
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.SummableInverseSquare

/-- The three symbolic cleared signs close the growing lower-six envelope at
every scale on which it is consumed.  Scales below 48 and the production tail
remain supplied by their independent exact proofs. -/
theorem growingResidualLowerSix_all_of_cleared
    (hWithin : ∀ D c : Nat, LowerSixWithinCenterCell D c →
      (0 : Q') ≤ lowerSixWithinCellClearedDrop D c)
    (hEvenOdd : ∀ p : Nat, 5 ≤ p →
      (0 : Q') ≤ lowerSixEvenOddEndpointClearedDrop p)
    (hOddEven : ∀ p : Nat, 5 ≤ p →
      (0 : Q') ≤ lowerSixOddEvenEndpointClearedDrop p) :
    ∀ k : Nat, 10 ≤ k → GrowingResidualLowerSix k := by
  intro k hk10
  by_cases hk8190 : 8190 ≤ k
  · exact growingResidualLowerSix_production (by omega)
  · by_cases hk48 : 48 ≤ k
    · exact growingResidualLowerSix_48_8189_of_cleared
        hWithin hEvenOdd hOddEven hk48 (by omega)
    · exact growingResidualLowerSix_below_forty_eight hk10 (by omega)

/-- All-scale physical Pascal cross resulting from the cleared signs and the
already-proved upper-eight envelope. -/
theorem physicalPascalCrossResidual_all_of_cleared
    (hWithin : ∀ D c : Nat, LowerSixWithinCenterCell D c →
      (0 : Q') ≤ lowerSixWithinCellClearedDrop D c)
    (hEvenOdd : ∀ p : Nat, 5 ≤ p →
      (0 : Q') ≤ lowerSixEvenOddEndpointClearedDrop p)
    (hOddEven : ∀ p : Nat, 5 ≤ p →
      (0 : Q') ≤ lowerSixOddEvenEndpointClearedDrop p) :
    ∀ k : Nat, PhysicalPascalCrossResidual k :=
  physicalPascalCrossResidual_all_of_growing_lower_six
    (growingResidualLowerSix_all_of_cleared
      hWithin hEvenOdd hOddEven)

/-- Exact coefficient-two harmonic mass-cross bound at every scale. -/
theorem harmonicMassCross_le_two_invSq_all_of_cleared
    (hWithin : ∀ D c : Nat, LowerSixWithinCenterCell D c →
      (0 : Q') ≤ lowerSixWithinCellClearedDrop D c)
    (hEvenOdd : ∀ p : Nat, 5 ≤ p →
      (0 : Q') ≤ lowerSixEvenOddEndpointClearedDrop p)
    (hOddEven : ∀ p : Nat, 5 ≤ p →
      (0 : Q') ≤ lowerSixOddEvenEndpointClearedDrop p)
    (k : Nat) :
    harmonicMassCross k ≤
      (Q'.ofNat 2 * invSqTerm 2 (by decide) k) *
        (harmonicD k * harmonicD (k + 1)) :=
  harmonicMassCross_le_two_invSq_of_physicalPascalCross k
    (physicalPascalCrossResidual_all_of_cleared
      hWithin hEvenOdd hOddEven k)

/-- The established harmonic character-GNS located gap satisfies its exact
adjacent-scale inequality at every scale under the same three signs. -/
theorem harmonicGNSMargin_singleStep_all_of_cleared
    (hWithin : ∀ D c : Nat, LowerSixWithinCenterCell D c →
      (0 : Q') ≤ lowerSixWithinCellClearedDrop D c)
    (hEvenOdd : ∀ p : Nat, 5 ≤ p →
      (0 : Q') ≤ lowerSixEvenOddEndpointClearedDrop p)
    (hOddEven : ∀ p : Nat, 5 ≤ p →
      (0 : Q') ≤ lowerSixOddEvenEndpointClearedDrop p)
    (k : Nat) :
    ((1 : Q') - BondMovingQuadratic.bondMovingDeltaRen 1
        UniformCouplingFromAF.pMult
          (HarmonicCutoffBoundary.harmW k)) *
        harmonicGNSMargin k ≤ harmonicGNSMargin (k + 1) :=
  harmonicGNSMargin_singleStep_of_cross
    (harmonicMassCross_le_two_invSq_all_of_cleared
      hWithin hEvenOdd hOddEven) k

/-- Positive all-scale floor for the already-constructed harmonic character
GNS margin.  This remains a harmonic-model theorem, not a physical Yang--Mills
continuum construction. -/
theorem harmonicGNS_multiscale_floor_all_of_cleared
    (hWithin : ∀ D c : Nat, LowerSixWithinCenterCell D c →
      (0 : Q') ≤ lowerSixWithinCellClearedDrop D c)
    (hEvenOdd : ∀ p : Nat, 5 ≤ p →
      (0 : Q') ≤ lowerSixEvenOddEndpointClearedDrop p)
    (hOddEven : ∀ p : Nat, 5 ≤ p →
      (0 : Q') ≤ lowerSixOddEvenEndpointClearedDrop p) :
    ∀ k : Nat,
      (1 - harmonicModelBudget) * canonicalHarmonicTrueMargin 0 - 0 ≤
          canonicalHarmonicTrueMargin k ∧
        (0 : Q') <
          (1 - harmonicModelBudget) * canonicalHarmonicTrueMargin 0 - 0 :=
  harmonicGNS_multiscale_floor_of_cross
    (harmonicMassCross_le_two_invSq_all_of_cleared
      hWithin hEvenOdd hOddEven)

#print axioms growingResidualLowerSix_all_of_cleared
#print axioms physicalPascalCrossResidual_all_of_cleared
#print axioms harmonicMassCross_le_two_invSq_all_of_cleared
#print axioms harmonicGNSMargin_singleStep_all_of_cleared
#print axioms harmonicGNS_multiscale_floor_all_of_cleared

end YMGap.Continuum.HarmonicMassCrossLowerSixRecoveryTraversalClosure
