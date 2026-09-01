/-
# Matched-tail feasibility gate for the assigned central-face ratio

The aggregate assigned-mass gate shows that a finite assigned-spin ratio
ceiling, multiplied by the excited spin-cube ray mass, must dominate the
physical non-vacuum stationary mass.  The matched dyadic same-action tail has
an independently proved vacuum calibration `pi(0) <= 5/6`.  Combining the two
facts forces the concrete product

    finite ratio ceiling * excited ray mass

to remain at least `1/6` at every matched scale `>= 2`.

This is a necessary condition, not a cofinal ratio bound and not an
obstruction by itself.  Proving that the ray mass vanishes, or instead proving
a matching ratio estimate, remains open.  No congestion, finite gap, physical
scaling, continuum theory, or Clay conclusion is proved here.

No `Classical`, choice, `native_decide`, `sorry`, new axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4DyadicCubeVacuumCalibration
import YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassAggregateGate

namespace YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedTailGate

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4DyadicCubeVacuumCalibration
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4MatchedPhysicalFarautTrajectory
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassAggregateGate
open YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassReturnReduction
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative

/-- On every calibrated matched dyadic tail scale, the sharp assigned-spin
ratio ceiling times the displayed excited ray mass is at least `1/6`. -/
theorem oneSixth_le_matchedAssignedRatioFiniteCeiling_mul_rayMass_tail
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    (bridge :
      MatchedDyadicSameActionAFBridge
        family law spacing coupling)
    {scale : Nat} (hscale : 2 ≤ scale) :
    let w := matchedAllSpinWeight family coupling scale
    let K := matchedAllSpinCutoff family coupling scale
    Q'.mkPos 1 6 (by decide) ≤
      positiveCentralFaceAssignedStationaryRatioFiniteCeiling
          (matchedAllSpinWeight_pos family coupling scale) K *
        centralLowerExcitedSpinCubeRayMass
          w (matchedAllSpinWeight_nonnegative family coupling scale) K := by
  exact
    oneSixth_le_finiteCeiling_mul_rayMass_of_vacuumMass_le_fiveSixths
      (matchedAllSpinWeight_pos family coupling scale)
      (one_le_matchedAllSpinCutoff bridge scale)
      (matchedVacuumRowMarginal_le_fiveSixths_tail bridge hscale)

end YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedTailGate

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorPositiveCentralFaceAssignedMassMatchedTailGate.oneSixth_le_matchedAssignedRatioFiniteCeiling_mul_rayMass_tail
