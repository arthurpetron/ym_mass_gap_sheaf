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
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualTransitionProductCompiler

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
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler.DynamicVacuumSectorObservablePin
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRescaledStrengthTracking
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicSpacingTailCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicStrengthNormalization
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualTransitionProductCompiler
open YMGap.Continuum.QuadraticRateErrorTailControl
open YMGap.Continuum.PhysicalSeparatorContinuumRealization
open YMGap.Continuum.PhysicalSeparatorFullLogComparison
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

/-- Add the independent finite exact-log ceiling to the matched Cauchy
consumer.  The result carries spacing cofinality, convergence, and the
surviving positive/finite rate bounds for the same completed carrier. -/
def matchedExactRateCutoffRemovalOfRescaledStrength
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
    (ceiling : FullRangeLogRateCeiling (fullRangeRateFamily pin))
    (C : AFTrajectoryCertificate)
    (H : ShiftedAFTrajectoryIdentification C trajectory.coupling) :
    ExactRateCutoffRemoval
      (DynamicVacuumSectorObservablePin.exactCertificate
        pin scaling.toPhysicalRateBand ceiling) :=
  exactRateCutoffRemovalOfRateCauchy
    pin scaling.toPhysicalRateBand ceiling
    (matchedExactLogRateCauchyOfRescaledStrength
      trajectory producer scaling pin variation C H)

namespace MatchedPhysicalDynamicExplicitRayEventualCanonicalCapacityCheckProducer

/-- The exact-log consumer specialized to the literal matched explicit
capacity-check producer.  Its projections remain definitionally tied to the
same completed carrier, transfer, and observable pin. -/
def matchedExplicitProducerExactLogRateCauchyOfRescaledStrength
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    (producer :
      MatchedPhysicalDynamicExplicitRayEventualCanonicalCapacityCheckProducer
        trajectory)
    (scaling : MatchedPhysicalDynamicStrengthScaling trajectory producer.toLocalProducer)
    (pin : DynamicVacuumSectorObservablePin
      (trajectory.toCompletedFamily producer.toLocalProducer))
    (variation : SummableRationalStepVariation
      (rescaledStrength
        (trajectory.toNormalizedStrengthLaw producer.toLocalProducer)))
    (C : AFTrajectoryCertificate)
    (H : ShiftedAFTrajectoryIdentification C trajectory.coupling) :
    CReal.ModCauchyEv ((fullRangeRateFamily pin).rate) :=
  matchedExactLogRateCauchyOfRescaledStrength
    trajectory producer.toLocalProducer scaling pin variation C H

end MatchedPhysicalDynamicExplicitRayEventualCanonicalCapacityCheckProducer

#print axioms matchedExactLogRateCauchyOfRescaledStrength
#print axioms matchedExactRateCutoffRemovalOfRescaledStrength
#print axioms
  MatchedPhysicalDynamicExplicitRayEventualCanonicalCapacityCheckProducer.matchedExplicitProducerExactLogRateCauchyOfRescaledStrength

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicRescaledStrengthCompiler
