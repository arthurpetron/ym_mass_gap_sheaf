/-
# Growing-volume low-spin to matched-ray comparison gate

The all-cutoff low-spin replication theorem makes the slice-zero spin-one
stationary marginal tend to zero when the reflection half grows.  The matched
cofinal obstruction instead uses the sum of the spin-cube states `1,...,K` at
fixed reflection half zero.  These are different normalized finite objects.

This module names the exact diagonal comparison that would connect them and
proves its downstream consequence.  The comparison structure is intentionally
not inhabited: no fixed-half/growing-half volume comparison, ray-sum bound,
all-vector gap, continuum limit, or Clay theorem is asserted here.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4LowSpinAllCutoffGrowingVolumeCompletionFactorization
import YMGap.Continuum.BF4DyadicCubeVacuumCalibration
import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayTailZeroNoGo

namespace YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate

set_option maxRecDepth 500000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4LowSpinAllCutoffGrowingVolumeCompletionFactorization
open YMGap.Continuum.BF4LowSpinGrowingVolumePositiveRawReplication
open YMGap.Continuum.BF4DyadicCubeVacuumCalibration
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedCofinalGate
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedRayTailZeroNoGo
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact missing comparison -/

/-- A diagonal comparison from the fixed-half matched spin-cube ray to a
cutoff- and scale-independent multiple of the single growing-half slice-zero
low-spin atom at the same matched cutoff and coupling.  These fields
deliberately expose both missing ingredients: control of the complete spin ray
by one low-spin atom and comparison of the normalized half-zero law with the
law at reflection half `scale + 1`. -/
structure MatchedDyadicLowSpinGrowingVolumeRayDomination
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (_bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling) : Type where
  ceiling : Q'
  ceiling_pos : (0 : Q') < ceiling
  rayMass_le_ceiling_mul_growingReference : ∀ scale,
    centralLowerExcitedSpinCubeRayMass
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) ≤
      ceiling *
        centralPhysicalRowMarginal
          (matchedAllSpinWeight family coupling scale)
          (Q'.le_of_lt
            (matchedAllSpinWeight_pos family coupling scale))
          (matchedAllSpinCutoff family coupling scale)
          (scale + 1)
          (lowSpinCentralReferenceState scale)

namespace MatchedDyadicLowSpinGrowingVolumeRayDomination

/-! ## 2. Compilation to the existing matched no-go branch -/

/-- The all-cutoff `1 / (volume + 1)` theorem turns the comparison field into
located tail-zero data for the exact fixed-half matched ray. -/
def toMatchedRayMassTailZero
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (comparison :
      MatchedDyadicLowSpinGrowingVolumeRayDomination bridge) :
    MatchedDyadicExcitedSpinCubeRayMassTailZero bridge where
  rate epsilon :=
    (Q'.divPos epsilon comparison.ceiling comparison.ceiling_pos).den
  rayMass_le := by
    intro epsilon hepsilon scale hscale
    let w := matchedAllSpinWeight family coupling scale
    let K := matchedAllSpinCutoff family coupling scale
    let delta :=
      Q'.divPos epsilon comparison.ceiling comparison.ceiling_pos
    have hw : (0 : Q') < w :=
      matchedAllSpinWeight_pos family coupling scale
    have hK : 1 ≤ K := one_le_matchedAllSpinCutoff bridge scale
    have hdelta : (0 : Q') < delta := by
      unfold delta
      exact Q'.divPos_pos epsilon comparison.ceiling
        comparison.ceiling_pos hepsilon
    have hscale' : delta.den ≤ scale := by
      simpa only [delta] using hscale
    have hgrowing := lowSpinCentralKReferenceMarginal_le_epsilon
      w hw K hK delta hdelta scale hscale'
    have hscaled :
        comparison.ceiling *
            centralPhysicalRowMarginal
              w (Q'.le_of_lt hw) K (scale + 1)
                (lowSpinCentralReferenceState scale) ≤
          comparison.ceiling * delta :=
      Q'.mul_le_mul_of_nonneg_left _ _ comparison.ceiling hgrowing
        (Q'.le_of_lt comparison.ceiling_pos)
    have hcollapse : comparison.ceiling * delta ≈ epsilon := by
      exact Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv comparison.ceiling delta)
        (by
          unfold delta
          exact Q'.divPos_mul_eqv epsilon comparison.ceiling
            comparison.ceiling_pos)
    exact Q'.le_trans' _ _ _
      (comparison.rayMass_le_ceiling_mul_growingReference scale)
      (Q'.le_trans' _ _ _
        (by simpa only [w, K] using hscaled)
        (Q'.le_of_eqv hcollapse))

/-- Consequently, inhabiting the exact comparison closes the cofinal assigned
stationary-ratio route as a no-go; it does not produce a spectral gap. -/
theorem excludes_cofinalAssignedRatio
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling}
    (comparison :
      MatchedDyadicLowSpinGrowingVolumeRayDomination bridge) :
    ¬ Nonempty
      (MatchedDyadicCofinalPositiveCentralFaceAssignedStationaryRatio
        bridge) :=
  tailZero_excludes_cofinalAssignedRatio
    comparison.toMatchedRayMassTailZero

end MatchedDyadicLowSpinGrowingVolumeRayDomination

end YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate

#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate.MatchedDyadicLowSpinGrowingVolumeRayDomination.toMatchedRayMassTailZero
#print axioms
  YMGap.Continuum.BF4LowSpinGrowingVolumeMatchedRayComparisonGate.MatchedDyadicLowSpinGrowingVolumeRayDomination.excludes_cofinalAssignedRatio
