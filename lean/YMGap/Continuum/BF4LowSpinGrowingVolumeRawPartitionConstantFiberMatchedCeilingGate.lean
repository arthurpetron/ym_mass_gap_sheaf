/-
# Matched ceiling gate for the finite constant-fiber switch

The finite constant-fiber construction supplies an exact positive ceiling at
every positive-coupling datum.  This module identifies the remaining cofinal
input without hiding it: one rational ceiling must dominate those explicit
datum-dependent ceilings along the complete matched trajectory.

Such a bound promotes the finite switches to the existing matched
weighted-fiber interface.  The bound is intentionally not inhabited here.
Finite positivity alone gives no cutoff- or volume-uniform estimate, and this
module asserts no cofinal contraction, operator gap, continuum limit, or Clay
theorem.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberMatchedCeilingGate

set_option maxRecDepth 500000
set_option maxHeartbeats 12000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4DyadicCubeVacuumCalibration
open YMGap.Continuum.BF4LowSpinAllCutoffGrowingVolumeCompletionFactorization
open YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberSwitching
open YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionFiberSwitchingGate
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov

/-! ## 1. Monotonicity of a finite switching ceiling -/

/-- Any valid weighted-fiber switch remains valid after increasing its
ceiling.  Target-weight nonnegativity is what makes this step constructive. -/
def weakenFiniteSwitchingCeiling
    {w : Q'} {hw : (0 : Q') ≤ w} {K volume : Nat}
    {smaller larger : Q'}
    (switching :
      LowSpinFixedGrowingRawPartitionFiberSwitching
        w hw K volume smaller)
    (hle : smaller ≤ larger) :
    LowSpinFixedGrowingRawPartitionFiberSwitching
      w hw K volume larger where
  repair := switching.repair
  repair_mem := switching.repair_mem
  weighted_fiber_capacity := by
    intro target htarget
    exact Q'.le_trans' _ _ _
      (switching.weighted_fiber_capacity target htarget)
      (Q'.mul_le_mul_of_nonneg_right
        smaller larger
        (fixedGrowingRawPartitionTargetIndexWeight
          w hw K volume target)
        hle
        (fixedGrowingRawPartitionTargetIndexWeight_nonnegative
          hw K volume target))

/-! ## 2. The exact matched analytic input -/

/-- The explicit finite ceiling evaluated on the matched coupling, cutoff,
and growing volume at one scale. -/
def matchedConstantFiberCeiling
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling)
    (scale : Nat) : Q' :=
  fixedGrowingRawPartitionConstantFiberCeiling
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_pos family coupling scale)
    (matchedAllSpinCutoff family coupling scale)
    (one_le_matchedAllSpinCutoff bridge scale)
    scale

theorem matchedConstantFiberCeiling_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (scale : Nat) :
    (0 : Q') < matchedConstantFiberCeiling bridge scale := by
  exact fixedGrowingRawPartitionConstantFiberCeiling_pos
    (matchedAllSpinWeight_pos family coupling scale)
    (one_le_matchedAllSpinCutoff bridge scale)
    scale

/-- The sole uniformity field needed to promote the explicit finite constant
switches to the existing matched weighted-fiber interface.  This is a genuine
analytic bound, not a consequence of finite search or positivity. -/
structure MatchedDyadicConstantFiberCeilingBound
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
    matchedConstantFiberCeiling bridge scale ≤ ceiling

namespace MatchedDyadicConstantFiberCeilingBound

/-- A uniform bound on the displayed finite ceilings promotes the explicit
constant repair at every scale to one matched switching family. -/
opaque toMatchedFiberSwitching
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (bound : MatchedDyadicConstantFiberCeilingBound bridge) :
    MatchedDyadicLowSpinRawPartitionFiberSwitching bridge :=
  { ceiling := bound.ceiling
    one_le_ceiling := bound.one_le_ceiling
    switching := by
      intro scale
      exact
        weakenFiniteSwitchingCeiling
          (fixedGrowingRawPartitionConstantFiberSwitching
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_pos family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (one_le_matchedAllSpinCutoff bridge scale)
            scale)
          (bound.matchedCeiling_le scale) }

/-- Consequently the uniform finite-ceiling bound yields the normalized
spin-one comparison at every matched scale.  Control of the remaining spin
ray is still a separate open producer. -/
theorem fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (bound : MatchedDyadicConstantFiberCeilingBound bridge)
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
        (fixedGrowingRawPartitionConstantFiberSwitching
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_pos family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (one_le_matchedAllSpinCutoff bridge scale)
          scale)
        (bound.matchedCeiling_le scale))

end MatchedDyadicConstantFiberCeilingBound

end YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberMatchedCeilingGate

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberMatchedCeilingGate.weakenFiniteSwitchingCeiling
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberMatchedCeilingGate.matchedConstantFiberCeiling_pos
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberMatchedCeilingGate.MatchedDyadicConstantFiberCeilingBound.toMatchedFiberSwitching
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeRawPartitionConstantFiberMatchedCeilingGate.MatchedDyadicConstantFiberCeilingBound.fixedHalfSpinOneMarginal_le_ceiling_mul_growingReference
