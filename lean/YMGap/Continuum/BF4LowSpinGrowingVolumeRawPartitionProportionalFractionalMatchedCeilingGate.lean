/-
# Matched aggregate-ratio gate for proportional fractional switching

The finite proportional kernel achieves the exact source/target occurrence
ratio.  This module evaluates that optimal fractional ceiling on the matched
dyadic trajectory and isolates the remaining analytic input: one rational
bound for the aggregate-ratio sequence.

Such a bound gives a matched raw cross at every scale.  It is strictly cleaner
than the one-target gate because no target-cardinality overhead remains, but
the bound is not constructed here.  No complete-spin-ray compression,
cofinal contraction, operator gap, continuum limit, or Clay theorem is
asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberMatchedCeilingGate
import YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionProportionalFractionalSwitching

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionProportionalFractionalMatchedCeilingGate

set_option maxRecDepth 500000
set_option maxHeartbeats 12000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4DyadicCubeVacuumCalibration
open YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberMatchedCeilingGate
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberRatioBracket
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionProportionalFractionalSwitching
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov

/-! ## 1. Exact matched aggregate-ratio sequence -/

def matchedCrossTotalRatio
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling)
    (scale : Nat) : Q' :=
  fixedGrowingRawPartitionCrossTotalRatio
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_pos family coupling scale)
    (matchedAllSpinCutoff family coupling scale)
    (one_le_matchedAllSpinCutoff bridge scale)
    scale

theorem matchedCrossTotalRatio_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (scale : Nat) :
    (0 : Q') < matchedCrossTotalRatio bridge scale := by
  exact fixedGrowingRawPartitionCrossTotalRatio_pos
    (matchedAllSpinWeight_pos family coupling scale)
    (one_le_matchedAllSpinCutoff bridge scale)
    scale

/-- The optimal fractional ceiling is no larger than the optimal one-target
ceiling at every matched scale. -/
theorem matchedCrossTotalRatio_le_maximumFiberCeiling
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (scale : Nat) :
    matchedCrossTotalRatio bridge scale ≤
      matchedMaximumFiberCeiling bridge scale := by
  exact fixedGrowingRawPartitionCrossTotalRatio_le_maximumFiberCeiling
    (matchedAllSpinWeight_pos family coupling scale)
    (one_le_matchedAllSpinCutoff bridge scale)
    scale

/-! ## 2. Uniform matched ratio-bound interface -/

structure MatchedDyadicCrossTotalRatioBound
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling) : Type where
  ceiling : Q'
  one_le_ceiling : (1 : Q') ≤ ceiling
  matchedRatio_le : ∀ scale,
    matchedCrossTotalRatio bridge scale ≤ ceiling

namespace MatchedDyadicCrossTotalRatioBound

/-- A uniform maximum-target bound automatically bounds the smaller optimal
fractional ratio sequence. -/
def ofMaximumFiberBound
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (bound : MatchedDyadicMaximumFiberCeilingBound bridge) :
    MatchedDyadicCrossTotalRatioBound bridge where
  ceiling := bound.ceiling
  one_le_ceiling := bound.one_le_ceiling
  matchedRatio_le := by
    intro scale
    exact Q'.le_trans' _ _ _
      (matchedCrossTotalRatio_le_maximumFiberCeiling scale)
      (bound.matchedCeiling_le scale)

/-- A uniform ratio bound weakens the exact proportional switch to one common
finite ceiling at each matched scale. -/
opaque toFiniteFractionalSwitching
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (bound : MatchedDyadicCrossTotalRatioBound bridge)
    (scale : Nat) :
    LowSpinFixedGrowingRawPartitionFractionalSwitching
      (matchedAllSpinWeight family coupling scale)
      (Q'.le_of_lt
        (matchedAllSpinWeight_pos family coupling scale))
      (matchedAllSpinCutoff family coupling scale)
      scale bound.ceiling :=
  weakenFiniteFractionalSwitchingCeiling
    (fixedGrowingRawPartitionProportionalFractionalSwitching
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_pos family coupling scale)
      (matchedAllSpinCutoff family coupling scale)
      (one_le_matchedAllSpinCutoff bridge scale)
      scale)
    (bound.matchedRatio_le scale)

/-- The uniform optimal-fractional ratio bound gives the matched crossed raw
inequality at every scale. -/
theorem rawCross
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (bound : MatchedDyadicCrossTotalRatioBound bridge)
    (scale : Nat) :
    fixedHalfSpinOneRawRow
        (matchedAllSpinWeight family coupling scale)
        (Q'.le_of_lt
          (matchedAllSpinWeight_pos family coupling scale))
        (matchedAllSpinCutoff family coupling scale) *
      growingHalfPhysicalPartition
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinCutoff family coupling scale) scale ≤
      (bound.ceiling *
          growingHalfSpinOneRawRow
            (matchedAllSpinWeight family coupling scale)
            (Q'.le_of_lt
              (matchedAllSpinWeight_pos family coupling scale))
            (matchedAllSpinCutoff family coupling scale) scale) *
        fixedHalfPhysicalPartition
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinCutoff family coupling scale) := by
  exact
    LowSpinFixedGrowingRawPartitionFractionalSwitching.rawCross
      (bound.toFiniteFractionalSwitching scale)

end MatchedDyadicCrossTotalRatioBound

end YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionProportionalFractionalMatchedCeilingGate

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionProportionalFractionalMatchedCeilingGate.matchedCrossTotalRatio_pos
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionProportionalFractionalMatchedCeilingGate.matchedCrossTotalRatio_le_maximumFiberCeiling
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionProportionalFractionalMatchedCeilingGate.MatchedDyadicCrossTotalRatioBound.ofMaximumFiberBound
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionProportionalFractionalMatchedCeilingGate.MatchedDyadicCrossTotalRatioBound.toFiniteFractionalSwitching
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionProportionalFractionalMatchedCeilingGate.MatchedDyadicCrossTotalRatioBound.rawCross
