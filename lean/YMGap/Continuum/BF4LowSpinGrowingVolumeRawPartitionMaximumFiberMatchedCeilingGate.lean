/-
# Matched ceiling gate for the maximum-target finite switch

The maximum-target constant repair has an exact ceiling no larger than the
earlier arbitrary-positive-target ceiling.  This module evaluates that sharper
sequence on the matched trajectory and isolates its still-open uniform bound.

A uniform maximum-ceiling bound is sufficient for the existing matched
weighted-fiber interface.  It is not constructed here, and a distributed
multi-target repair could remain strictly better than every constant repair.
No cofinal contraction, operator gap, continuum limit, or Clay theorem is
asserted.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberMatchedCeilingGate
import YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberSwitching

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberMatchedCeilingGate

set_option maxRecDepth 500000
set_option maxHeartbeats 12000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4DyadicCubeVacuumCalibration
open YMGap.Continuum.BF4LowSpinAllCutoffGrowingVolumeCompletionFactorization
open YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberMatchedCeilingGate
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionFiberSwitchingGate
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberSwitching
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov

/-! ## 1. The sharper matched ceiling sequence -/

def matchedMaximumFiberCeiling
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling)
    (scale : Nat) : Q' :=
  fixedGrowingRawPartitionMaximumFiberCeiling
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_pos family coupling scale)
    (matchedAllSpinCutoff family coupling scale)
    (one_le_matchedAllSpinCutoff bridge scale)
    scale

theorem matchedMaximumFiberCeiling_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (scale : Nat) :
    (0 : Q') < matchedMaximumFiberCeiling bridge scale := by
  exact fixedGrowingRawPartitionMaximumFiberCeiling_pos
    (matchedAllSpinWeight_pos family coupling scale)
    (one_le_matchedAllSpinCutoff bridge scale)
    scale

theorem matchedMaximumFiberCeiling_le_constant
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (scale : Nat) :
    matchedMaximumFiberCeiling bridge scale ≤
      matchedConstantFiberCeiling bridge scale := by
  exact fixedGrowingRawPartitionMaximumFiberCeiling_le_constant
    (matchedAllSpinWeight_pos family coupling scale)
    (one_le_matchedAllSpinCutoff bridge scale)
    scale

/-! ## 2. Uniform-bound producer interface -/

structure MatchedDyadicMaximumFiberCeilingBound
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling) : Type where
  ceiling : Q'
  one_le_ceiling : (1 : Q') ≤ ceiling
  matchedCeiling_le : ∀ scale,
    matchedMaximumFiberCeiling bridge scale ≤ ceiling

namespace MatchedDyadicMaximumFiberCeilingBound

/-- Any bound on the earlier arbitrary-target sequence bounds the sharper
maximum-target sequence. -/
def ofConstantBound
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (bound : MatchedDyadicConstantFiberCeilingBound bridge) :
    MatchedDyadicMaximumFiberCeilingBound bridge where
  ceiling := bound.ceiling
  one_le_ceiling := bound.one_le_ceiling
  matchedCeiling_le := by
    intro scale
    exact Q'.le_trans' _ _ _
      (matchedMaximumFiberCeiling_le_constant scale)
      (bound.matchedCeiling_le scale)

/-- A uniform bound on the sharper finite ceilings promotes the
maximum-target repair at every scale to one matched switching family. -/
opaque toMatchedFiberSwitching
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (bound : MatchedDyadicMaximumFiberCeilingBound bridge) :
    MatchedDyadicLowSpinRawPartitionFiberSwitching bridge :=
  { ceiling := bound.ceiling
    one_le_ceiling := bound.one_le_ceiling
    switching := by
      intro scale
      exact
        weakenFiniteSwitchingCeiling
          (fixedGrowingRawPartitionMaximumFiberSwitching
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_pos family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (one_le_matchedAllSpinCutoff bridge scale)
            scale)
          (bound.matchedCeiling_le scale) }

/-- The sharper uniform ceiling therefore gives the matched normalized
spin-one comparison.  Complete-ray compression remains separate. -/
theorem fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (bound : MatchedDyadicMaximumFiberCeilingBound bridge)
    (scale : Nat) :
    centralPhysicalRowMarginal
        (matchedAllSpinWeight family coupling scale)
        (Q'.le_of_lt
          (matchedAllSpinWeight_pos family coupling scale))
        (matchedAllSpinCutoff family coupling scale) 0
        (centralLowerSpinCubeState 1) ≤
      bound.ceiling *
        centralPhysicalRowMarginal
          (matchedAllSpinWeight family coupling scale)
          (Q'.le_of_lt
            (matchedAllSpinWeight_pos family coupling scale))
          (matchedAllSpinCutoff family coupling scale)
          (scale + 1)
          (lowSpinCentralReferenceState scale) := by
  exact
    LowSpinFixedGrowingRawPartitionFiberSwitching.fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
      (matchedAllSpinWeight_pos family coupling scale)
      (one_le_matchedAllSpinCutoff bridge scale)
      scale
      (weakenFiniteSwitchingCeiling
        (fixedGrowingRawPartitionMaximumFiberSwitching
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_pos family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (one_le_matchedAllSpinCutoff bridge scale)
          scale)
        (bound.matchedCeiling_le scale))

end MatchedDyadicMaximumFiberCeilingBound

end YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberMatchedCeilingGate

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberMatchedCeilingGate.matchedMaximumFiberCeiling_pos
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberMatchedCeilingGate.matchedMaximumFiberCeiling_le_constant
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberMatchedCeilingGate.MatchedDyadicMaximumFiberCeilingBound.ofConstantBound
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberMatchedCeilingGate.MatchedDyadicMaximumFiberCeilingBound.toMatchedFiberSwitching
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionMaximumFiberMatchedCeilingGate.MatchedDyadicMaximumFiberCeilingBound.fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
