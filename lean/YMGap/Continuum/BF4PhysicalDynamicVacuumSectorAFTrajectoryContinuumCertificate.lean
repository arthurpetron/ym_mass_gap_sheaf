/-
# Historical AF-to-continuum compiler with incompatible joint inputs

The AF trajectory module already proves summable variation for its shifted
coupling. The completed BF4 family, however, uses its own physical gap. The
proposed numerator calibration was

  latticeMargin j ≈ shiftedTau C j * spacing j.

Both consumers in this module require that calibration together with a
positive `DynamicVacuumSectorPhysicalRateBand`. Those inputs cannot coexist:
`AFTrajectoryPhysicalGapCalibrationObstruction` constructs a scale where the
vanishing AF coupling is strictly below the physical gap's positive floor.
The conditional declarations and their original types are preserved, but
this route is refuted, not merely waiting for a calibration producer.

The AF scalar variation result and the direct same-family physical-gap
variation route are unaffected. No continuum or Yang--Mills nonexistence
conclusion follows from this incompatibility.

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

/-- Historical exact-rate compiler on the same separator selected by `pin`.
The implicit `band` and explicit `calibration` are incompatible by
`AFTrajectoryPhysicalGapCalibrationObstruction`. -/
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

/-- Historical conditional constructor, retaining all same-object fields.
Its positive `band` and AF `calibration` are incompatible by
`AFTrajectoryPhysicalGapCalibrationObstruction`; this is not a viable
producer path for a continuum certificate. -/
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
