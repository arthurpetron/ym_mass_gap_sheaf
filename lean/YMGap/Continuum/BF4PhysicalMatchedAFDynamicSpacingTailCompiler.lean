/-
# Matched-AF dynamic spacing tail compiler

The exact-log cutoff compiler consumes an inverse-square tail for the
physical spacing of the *same* completed dynamic family.  The AF chart
already proves this tail for an envelope evaluated on a coupling sequence
identified with a shifted AF trajectory.  This module transports that result
to the matched dynamic-family interface without changing the coupling,
spacing, or completed transfer.

This discharges the spacing branch of the forward/backward meet.  It does not
construct the local matched producer, the physical rate band, the
same-family gap variation, an observable pin, a projective OS handoff, or the
continuum Yang--Mills/Clay conclusion.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or `noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
import YMGap.Continuum.BF4AFPhysicalSpacingInverseSquare

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicSpacingTailCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.BF4AFPhysicalSpacingInverseSquare
open YMGap.Continuum.BF4AFPhysicalSpacingToZero
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.QuadraticRateErrorTailControl

namespace MatchedPhysicalDynamicScalarTrajectory

/-! ## Forward spacing branch -/

/-!
The AF inverse-square spacing tail transported to the exact matched dynamic
trajectory.  The target is the spacing carried by the trajectory's adaptive
scalar view, so the later completed-family spacing is definitionally the same
object.
-/
def physicalSpacingInverseSquareOfAFTrajectory
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (C : AFTrajectoryCertificate)
    (H : ShiftedAFTrajectoryIdentification C trajectory.coupling) :
    InverseSquareSpacingTail
      trajectory.toAdaptiveScalarTrajectory.transferSpacing 0 := by
  simpa only [MatchedPhysicalDynamicScalarTrajectory.toAdaptiveScalarTrajectory,
    matchedPhysicalDynamicSpacing,
    YMGap.Continuum.BF4AFPhysicalSpacingToZero.physicalSpacingOfEnvelope] using
    (spacingInverseSquareTailOfAFTrajectory spacing trajectory.coupling
      trajectory.coupling_pos trajectory.coupling_le_window C H)

end MatchedPhysicalDynamicScalarTrajectory

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicSpacingTailCompiler

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicSpacingTailCompiler.MatchedPhysicalDynamicScalarTrajectory.physicalSpacingInverseSquareOfAFTrajectory
