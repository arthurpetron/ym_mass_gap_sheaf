/-
# The constructive certificate gate for the dynamic BF4 continuum route

The continuum-facing data are not a bare existential endpoint.  They consist
of one fixed finite-to-continuum approximant (the exact logarithmic rate
sequence), an explicit Cauchy modulus and positive floor, and comparison and
descent witnesses tying the sampled finite observable to one projective OS
thread and one reconstructed spectral channel.

`DynamicVacuumSectorContinuumCertificate` makes that payload explicit.  Its
fields are deliberately the same-object fields already used by
`DynamicVacuumSectorContinuumHandoff`; `toHandoff` therefore loses no
provenance, while `ofHandoff` records that the floor is the one compiled from
the physical separator rather than an unrelated continuum lower bound.

This is a certificate gate, not a new analytic theorem: no continuum measure,
OS reconstruction, rate modulus, or exact-rate comparison is inhabited here.
The remaining inputs stay visible and can be supplied only by their genuine
constructive producers.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumCertificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.ExactRateReconstructionHandoff
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.MeasureLinkedOSReconstruction
open YMGap.Continuum.ProjectiveOSCorrelationHandoff
open YMGap.Continuum.PhysicalSeparatorFullLogComparison
open YMGap.Continuum.PhysicalSeparatorLinearTail
open YMGap.Continuum.PhysicalSeparatorContinuumRealization
open YMGap.Continuum.UnifiedContinuumFloor

/-! ## 1. The fixed approximant and its explicit payload -/

/-- The exact logarithmic physical-rate sequence attached to the same
completed separator and spacing.  This is the approximating object consumed
by the continuum certificate; it is not a freely chosen sequence. -/
def rateApproximant
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    {pin : DynamicVacuumSectorObservablePin family}
    {band : DynamicVacuumSectorPhysicalRateBand family}
    {ceiling : FullRangeLogRateCeiling
      (DynamicVacuumSectorObservablePin.fullRangeRateFamily pin)} :
    Nat → CReal :=
  (DynamicVacuumSectorObservablePin.exactCertificate pin band ceiling).rateFamily.rate

/-- A continuum certificate carrying the constructive payload demanded by the
discrete-to-continuous passage: rate modulus, positive uniform floor, sampled
comparison/projective descent, spectral-channel descent, and exact-rate
identification.  Every field is tied to the same `pin`, `band`, `ceiling`,
measure, and OS reconstruction. -/
structure DynamicVacuumSectorContinuumCertificate
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (pin : DynamicVacuumSectorObservablePin family)
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (ceiling : FullRangeLogRateCeiling
      (DynamicVacuumSectorObservablePin.fullRangeRateFamily pin))
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (existence : ContinuumYMExistence mu)
    (osGNS : MeasureLinkedOSGNSData existence) : Type 2 where
  /-- Explicit modulus of Cauchy stability for the fixed exact-rate sequence. -/
  rateCauchy : CReal.ModCauchyEv
    (rateApproximant (pin := pin) (band := band) (ceiling := ceiling))
  /-- Positive constructive-real floor for that same exact-rate sequence. -/
  rateFloor : CRealFloor
    (rateApproximant (pin := pin) (band := band) (ceiling := ceiling))
  /-- The floor is definitionally the one compiled from the finite physical
  separator certificate, not an unrelated lower bound. -/
  rateFloor_eq_compiled :
    rateFloor =
      FullRangeExactPhysicalSeparatorCertificate.exactRateCRealFloor
        (DynamicVacuumSectorObservablePin.exactCertificate pin band ceiling)
  /-- Same-object finite sampled correlator versus the fixed stage evaluator. -/
  projectiveOS : ProjectiveOSCorrelationHandoff
    pin.toPhysicalSeparator existence osGNS pin.physicalSampling
  /-- Descent of the same correlator to the reconstructed spectral channel. -/
  spectralChannel :
    ProjectiveOSCorrelationHandoff.ReconstructionSpectralChannelHandoff
      projectiveOS osGNS.reconstruction
  /-- Convergence of the same exact-rate approximants to the reconstruction's
  logarithmic gap. -/
  exactRate : ExactRateReconstructionHandoff
    (DynamicVacuumSectorObservablePin.exactCertificate pin band ceiling)
    osGNS.reconstruction

namespace DynamicVacuumSectorContinuumCertificate

/-! ## 2. Certificate projections and the existing commuting square -/

/-- The spacing modulus is part of the fixed dynamic family and is exposed by
the certificate gate rather than inferred after the fact. -/
def spacingModulus
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    {pin : DynamicVacuumSectorObservablePin family}
    {band : DynamicVacuumSectorPhysicalRateBand family}
    {ceiling : FullRangeLogRateCeiling
      (DynamicVacuumSectorObservablePin.fullRangeRateFamily pin)}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {existence : ContinuumYMExistence mu}
    {osGNS : MeasureLinkedOSGNSData existence}
    (_certificate : DynamicVacuumSectorContinuumCertificate
      pin band ceiling existence osGNS) : SpacingToZero family.transferSpacing :=
  family.transferSpacingToZero

/-- The certificate's positive floor remains explicit in rational currency. -/
theorem rateFloor_pos
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    {pin : DynamicVacuumSectorObservablePin family}
    {band : DynamicVacuumSectorPhysicalRateBand family}
    {ceiling : FullRangeLogRateCeiling
      (DynamicVacuumSectorObservablePin.fullRangeRateFamily pin)}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {existence : ContinuumYMExistence mu}
    {osGNS : MeasureLinkedOSGNSData existence}
    (certificate : DynamicVacuumSectorContinuumCertificate
      pin band ceiling existence osGNS) :
    (0 : Q') < certificate.rateFloor.floor :=
  certificate.rateFloor.floor_pos

/-- Forgetting only the named floor payload reconstructs the existing
same-object handoff.  No correlator, rate sequence, or reconstruction can be
changed by this contraction. -/
def toHandoff
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    {pin : DynamicVacuumSectorObservablePin family}
    {band : DynamicVacuumSectorPhysicalRateBand family}
    {ceiling : FullRangeLogRateCeiling
      (DynamicVacuumSectorObservablePin.fullRangeRateFamily pin)}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {existence : ContinuumYMExistence mu}
    {osGNS : MeasureLinkedOSGNSData existence}
    (certificate : DynamicVacuumSectorContinuumCertificate
      pin band ceiling existence osGNS) :
    DynamicVacuumSectorContinuumHandoff
      pin band ceiling existence osGNS where
  rateCauchy := certificate.rateCauchy
  projectiveOS := certificate.projectiveOS
  spectralChannel := certificate.spectralChannel
  exactRate := certificate.exactRate

/-- Every existing handoff can be re-presented as the explicit certificate
payload, with the floor inherited from the exact physical separator. -/
def ofHandoff
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    {pin : DynamicVacuumSectorObservablePin family}
    {band : DynamicVacuumSectorPhysicalRateBand family}
    {ceiling : FullRangeLogRateCeiling
      (DynamicVacuumSectorObservablePin.fullRangeRateFamily pin)}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {existence : ContinuumYMExistence mu}
    {osGNS : MeasureLinkedOSGNSData existence}
    (handoff : DynamicVacuumSectorContinuumHandoff
      pin band ceiling existence osGNS) :
    DynamicVacuumSectorContinuumCertificate
      pin band ceiling existence osGNS where
  rateCauchy := handoff.rateCauchy
  rateFloor :=
    FullRangeExactPhysicalSeparatorCertificate.exactRateCRealFloor
      (DynamicVacuumSectorObservablePin.exactCertificate pin band ceiling)
  rateFloor_eq_compiled := rfl
  projectiveOS := handoff.projectiveOS
  spectralChannel := handoff.spectralChannel
  exactRate := handoff.exactRate

/-- The explicit certificate gate still compiles to the standard same-object
continuum realization. -/
def toContinuumRealization
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    {pin : DynamicVacuumSectorObservablePin family}
    {band : DynamicVacuumSectorPhysicalRateBand family}
    {ceiling : FullRangeLogRateCeiling
      (DynamicVacuumSectorObservablePin.fullRangeRateFamily pin)}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {existence : ContinuumYMExistence mu}
    {osGNS : MeasureLinkedOSGNSData existence}
    (certificate : DynamicVacuumSectorContinuumCertificate
      pin band ceiling existence osGNS) :
    PhysicalSeparatorContinuumRealization
      (DynamicVacuumSectorObservablePin.exactCertificate pin band ceiling) mu :=
  certificate.toHandoff.toContinuumRealization

end DynamicVacuumSectorContinuumCertificate

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumCertificate

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumCertificate.DynamicVacuumSectorContinuumCertificate.toHandoff
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumCertificate.DynamicVacuumSectorContinuumCertificate.ofHandoff
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumCertificate.DynamicVacuumSectorContinuumCertificate.toContinuumRealization
