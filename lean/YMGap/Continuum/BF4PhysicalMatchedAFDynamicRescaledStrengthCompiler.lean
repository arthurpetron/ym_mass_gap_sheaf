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
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualAdaptiveObservableTransitionProductCompiler
import YMGap.Continuum.FinitePrefixFullLogRateCeiling
import YMGap.Continuum.PhysicalSeparatorFullLogHalfWindow

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
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualAdaptiveObservableTransitionProductCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewActiveRowSupportActivationDeletedAllCutoffObservableCompiler
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.ExactRateReconstructionHandoff
open YMGap.Continuum.FinitePrefixFullLogRateCeiling
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.MeasureLinkedOSReconstruction
open YMGap.Continuum.ProjectiveOSCorrelationHandoff
open YMGap.Continuum.QuadraticRateErrorTailControl
open YMGap.Continuum.PhysicalSeparatorContinuumRealization
open YMGap.Continuum.PhysicalSeparatorFullLogHalfWindow
open YMGap.Continuum.PhysicalSeparatorFullLogComparison
open YMGap.Continuum.SummableRationalStepVariation

/-! ## 0. The rate band computes the exact full-range ceiling -/

/-
The exact-log consumer previously accepted a separate finite ceiling.  For a
matched completed carrier this is not an independent analytic input: the
physical-rate band supplies the eventual half-window and the same upper rate
bound, while the finite-prefix ceiling is computed from the separator and its
positive spacing.  This constructor keeps every quantity on the pinned
completed family and removes that free ceiling field from the route.
-/

def fullRangeLogRateCeilingOfPhysicalRateBand
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (pin : DynamicVacuumSectorObservablePin family)
    (band : DynamicVacuumSectorPhysicalRateBand family) :
    FullRangeLogRateCeiling (fullRangeRateFamily pin) := by
  let start := band.marginModulus HalfPow.half
  let H : EventualSeparatorHalfWindow pin.toPhysicalSeparator start := {
    sep_ge_half := fun j hj => by
      have hrate := band.one_sub_epsilon_le_rate
        HalfPow.half (by decide) j hj
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (by decide : Q'.eqv HalfPow.half (1 - HalfPow.half))) hrate
  }
  let U : TailMarginRateCeiling pin.toPhysicalSeparator
      family.transferSpacing start := {
    ceiling := band.ceiling
    margin_bound := fun j hj => by
      have hmargin :=
        marginRate_eqv_physicalGap pin j
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hmargin)
        (band.physicalGap_le_ceiling j)
  }
  exact globalExactCeilingOfPrefixEventualHalfWindow
    pin.toPhysicalSeparator family.transferSpacing start
    (computedPrefixCeiling (fullRangeRateFamily pin) start) H U

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

/-! The preceding consumer is retained for callers that already carry an
explicit ceiling.  This variant computes that ceiling from the same physical
rate band, so the matched route has no free full-range upper-bound input. -/

def matchedExactRateCutoffRemovalOfRescaledStrengthOfPhysicalRateBand
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
    ExactRateCutoffRemoval
      (DynamicVacuumSectorObservablePin.exactCertificate
        pin scaling.toPhysicalRateBand
        (fullRangeLogRateCeilingOfPhysicalRateBand
          pin scaling.toPhysicalRateBand)) :=
  matchedExactRateCutoffRemovalOfRescaledStrength
    trajectory producer scaling pin variation
    (fullRangeLogRateCeilingOfPhysicalRateBand
      pin scaling.toPhysicalRateBand) C H

/-- Assemble the same-object continuum handoff from the matched exact-rate
certificate and the independent projective/OS/reconstruction witnesses. -/
def matchedContinuumHandoffOfRescaledStrength
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
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {existence : ContinuumYMExistence mu}
    {osGNS : MeasureLinkedOSGNSData existence}
    (projectiveOS : ProjectiveOSCorrelationHandoff pin.toPhysicalSeparator
      existence osGNS pin.physicalSampling)
    (spectralChannel :
      ProjectiveOSCorrelationHandoff.ReconstructionSpectralChannelHandoff
        projectiveOS osGNS.reconstruction)
    (exactRate : ExactRateReconstructionHandoff
      (DynamicVacuumSectorObservablePin.exactCertificate
        pin scaling.toPhysicalRateBand ceiling) osGNS.reconstruction)
    (C : AFTrajectoryCertificate)
    (H : ShiftedAFTrajectoryIdentification C trajectory.coupling) :
    DynamicVacuumSectorContinuumHandoff
      pin scaling.toPhysicalRateBand ceiling existence osGNS where
  rateCauchy := matchedExactLogRateCauchyOfRescaledStrength
    trajectory producer scaling pin variation C H
  projectiveOS := projectiveOS
  spectralChannel := spectralChannel
  exactRate := exactRate

/-- The matched observable-certificate route reaches exact-rate cutoff removal
on the completed carrier constructed from those literal certificates. -/
def observableCertificatesExactRateCutoffRemovalOfRescaledStrength
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (certificates : forall physicalScale,
      MatchedEventualNewEndpointTrafficOldNewFaceActivatedDeletedSupportAllCutoffObservableCertificate
        trajectory transitionStart physicalScale)
    (scaling : MatchedPhysicalDynamicStrengthScaling trajectory
      (observableCertificatesToLocalProducer transitionStart certificates))
    (pin : DynamicVacuumSectorObservablePin
      (observableCertificatesToCompletedFamily transitionStart certificates))
    (variation : SummableRationalStepVariation
      (rescaledStrength
        (observableCertificatesToNormalizedStrengthLaw
          transitionStart certificates)))
    (ceiling : FullRangeLogRateCeiling (fullRangeRateFamily pin))
    (C : AFTrajectoryCertificate)
    (H : ShiftedAFTrajectoryIdentification C trajectory.coupling) :
    ExactRateCutoffRemoval
      (DynamicVacuumSectorObservablePin.exactCertificate
        pin scaling.toPhysicalRateBand ceiling) :=
  matchedExactRateCutoffRemovalOfRescaledStrength
    trajectory (observableCertificatesToLocalProducer transitionStart certificates)
    scaling pin variation ceiling C H

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
#print axioms fullRangeLogRateCeilingOfPhysicalRateBand
#print axioms matchedExactRateCutoffRemovalOfRescaledStrength
#print axioms matchedExactRateCutoffRemovalOfRescaledStrengthOfPhysicalRateBand
#print axioms matchedContinuumHandoffOfRescaledStrength
#print axioms observableCertificatesExactRateCutoffRemovalOfRescaledStrength
#print axioms
  MatchedPhysicalDynamicExplicitRayEventualCanonicalCapacityCheckProducer.matchedExplicitProducerExactLogRateCauchyOfRescaledStrength

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicRescaledStrengthCompiler
