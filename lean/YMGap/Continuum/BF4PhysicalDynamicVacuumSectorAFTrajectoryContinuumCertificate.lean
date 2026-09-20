/-
# Compile the explicit AF/physical-gap bridge into the full continuum gate

The AF trajectory module already proves summable variation for its shifted
coupling.  The completed BF4 family, however, uses its own physical gap.  The
only honest bridge is the explicit numerator calibration

  latticeMargin j ≈ shiftedTau C j * spacing j.

This module consumes that calibration, the independently supplied inverse-
square spacing tail, and the already named same-object OS/GNS handoff fields.
It therefore constructs a `DynamicVacuumSectorContinuumCertificate` without
manufacturing any of those open inputs.  In particular, this is a compiler
from certificates, not a proof that the calibration, continuum existence, or
OS reconstruction exists.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.AFTrajectorySummableVariation
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumCertificate

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorAFTrajectoryContinuumCertificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.AFTrajectorySummableVariation
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumCertificate
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.ExactRateReconstructionHandoff
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.MeasureLinkedOSReconstruction
open YMGap.Continuum.PhysicalSeparatorFullLogComparison
open YMGap.Continuum.ProjectiveOSCorrelationHandoff
open YMGap.Continuum.QuadraticRateErrorTailControl

/-! ## The same-object forward/backward compiler -/

/-- Compile the AF recurrence plus the explicit same-family numerator
calibration into the exact logarithmic Cauchy field required by the full
continuum certificate.  The target is the rate sequence of the *same* exact
physical separator selected by `pin`, not a separately chosen AF sequence. -/
def exactRateCauchyOfAFTrajectoryNumeratorCalibration
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    {pin : DynamicVacuumSectorObservablePin family}
    {band : DynamicVacuumSectorPhysicalRateBand family}
    {ceiling : FullRangeLogRateCeiling
      (DynamicVacuumSectorObservablePin.fullRangeRateFamily pin)}
    (C : AFTrajectoryCertificate)
    (spacingTail : InverseSquareSpacingTail family.transferSpacing 0)
    (calibration : PhysicalGapNumeratorCalibration family C) :
    CReal.ModCauchyEv
      (rateApproximant (pin := pin) (band := band) (ceiling := ceiling)) := by
  simpa [rateApproximant,
    DynamicVacuumSectorObservablePin.exactCertificate] using
    (exactLogRateCauchyOfAFTrajectoryOfNumeratorCalibration
      pin band spacingTail calibration)

/-- The minimal conditional constructor for the full continuum certificate.

The forward side contributes the fixed completed observable, physical rate
band, and already supplied OS/projective fields.  The backward side
contributes exactly the AF trajectory, inverse-square spacing tail, and
same-object numerator calibration needed for the rate modulus.  No field is
weakened to an unrelated bound, and no missing analytic witness is inferred. -/
def DynamicVacuumSectorContinuumCertificate.ofAFTrajectoryNumeratorCalibration
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (pin : DynamicVacuumSectorObservablePin family)
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (ceiling : FullRangeLogRateCeiling
      (DynamicVacuumSectorObservablePin.fullRangeRateFamily pin))
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (existence : ContinuumYMExistence mu)
    (osGNS : MeasureLinkedOSGNSData existence)
    (C : AFTrajectoryCertificate)
    (spacingTail : InverseSquareSpacingTail family.transferSpacing 0)
    (calibration : PhysicalGapNumeratorCalibration family C)
    (projectiveOS : ProjectiveOSCorrelationHandoff
      pin.toPhysicalSeparator existence osGNS pin.physicalSampling)
    (spectralChannel :
      ProjectiveOSCorrelationHandoff.ReconstructionSpectralChannelHandoff
        projectiveOS osGNS.reconstruction)
    (exactRate : ExactRateReconstructionHandoff
      (DynamicVacuumSectorObservablePin.exactCertificate pin band ceiling)
      osGNS.reconstruction) :
    DynamicVacuumSectorContinuumCertificate
      pin band ceiling existence osGNS where
  rateCauchy := exactRateCauchyOfAFTrajectoryNumeratorCalibration
    C spacingTail calibration
  rateFloor :=
    FullRangeExactPhysicalSeparatorCertificate.exactRateCRealFloor
      (DynamicVacuumSectorObservablePin.exactCertificate pin band ceiling)
  rateFloor_eq_compiled := rfl
  projectiveOS := projectiveOS
  spectralChannel := spectralChannel
  exactRate := exactRate

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorAFTrajectoryContinuumCertificate

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorAFTrajectoryContinuumCertificate.exactRateCauchyOfAFTrajectoryNumeratorCalibration
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorAFTrajectoryContinuumCertificate.DynamicVacuumSectorContinuumCertificate.ofAFTrajectoryNumeratorCalibration
