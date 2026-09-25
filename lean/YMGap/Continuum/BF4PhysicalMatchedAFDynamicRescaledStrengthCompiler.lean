/-
# Matched AF trajectory into the rescaled-strength exact-log consumer

The matched physical trajectory already carries the exact coupling-dependent
spacing.  Its AF identification supplies the inverse-square spacing tail;
the rescaled-strength compiler then consumes that tail on the same completed
carrier.  This adapter does not construct the local producer, a strength
scaling certificate, an observable pin, or the rescaled-strength variation.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRescaledStrengthTracking
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicSpacingTailCompiler
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicStrengthNormalization

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicRescaledStrengthCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.BF4AFPhysicalSpacingToZero
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRescaledStrengthTracking
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicSpacingTailCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicStrengthNormalization
open YMGap.Continuum.QuadraticRateErrorTailControl
open YMGap.Continuum.SummableRationalStepVariation

/-- The matched AF spacing tail and the rescaled-strength variation compile
to an exact-log Cauchy modulus for the full-range rate of the same completed
matched carrier.  All remaining analytic inputs are explicit in the type. -/
def matchedExactLogRateCauchyOfRescaledStrength
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (producer : trajectory.LocalProducer)
    (scaling : MatchedPhysicalDynamicStrengthScaling trajectory producer)
    (pin : DynamicVacuumSectorObservablePin
      (trajectory.toCompletedFamily producer))
    (variation : SummableRationalStepVariation
      (rescaledStrength (trajectory.toNormalizedStrengthLaw producer)))
    (C : AFTrajectoryCertificate)
    (H : ShiftedAFTrajectoryIdentification C trajectory.coupling) :
    CReal.ModCauchyEv ((fullRangeRateFamily pin).rate) := by
  let band := scaling.toStrengthBand
  have hspacing :
      InverseSquareSpacingTail
        (trajectory.toCompletedFamily producer).transferSpacing 0 := by
    simpa only [MatchedPhysicalDynamicScalarTrajectory.toCompletedFamily,
      DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.toCompletedFamily] using
      (MatchedPhysicalDynamicScalarTrajectory.physicalSpacingInverseSquareOfAFTrajectory
        trajectory C H)
  exact exactLogRateCauchyOfRescaledStrength pin band variation hspacing

#print axioms matchedExactLogRateCauchyOfRescaledStrength

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicRescaledStrengthCompiler
