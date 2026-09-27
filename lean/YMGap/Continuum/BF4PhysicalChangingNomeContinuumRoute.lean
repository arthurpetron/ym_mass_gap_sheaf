/-
# Conditional continuum route for the repaired changing-nome observable

The preceding module reaches the observable-connected physical separator.
This module packages the remaining exact-rate, projective/OS, and spectral
identification inputs against that same separator and the same completed
family.  It is a dependency-preserving handoff, not a construction of any of
those analytic inputs.
-/

import YMGap.Continuum.BF4PhysicalChangingNomeObservableRoute
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization

namespace YMGap.Continuum.BF4PhysicalChangingNomeContinuumRoute

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalChangingNomeObservableRoute
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.MeasureLinkedOSReconstruction
open YMGap.Continuum.PhysicalSeparatorContinuumRealization
open YMGap.Continuum.PhysicalSeparatorFullLogComparison

/-! ## 1. The minimal exact continuum handoff certificate -/

/-- The remaining continuum inputs are attached to the rationalized
same-object route.  The dependent types prevent replacing its separator,
spacing schedule, rate certificate, or reconstruction after the fact. -/
structure ChangingNomeCarrierNormalizedContinuumRoute
    {M : Nat → Type} {mu : ContinuumMeasure M}
    (existence : ContinuumYMExistence mu)
    (osGNS : MeasureLinkedOSGNSData existence) : Type 3 where
  observable : ChangingNomeCarrierNormalizedObservableRoute
  ceiling : FullRangeLogRateCeiling
    (DynamicVacuumSectorObservablePin.fullRangeRateFamily
      observable.toObservablePin)
  handoff :
    DynamicVacuumSectorObservablePin.DynamicVacuumSectorContinuumHandoff
      observable.toObservablePin
      observable.cofinal.toPhysicalRateBand
      ceiling existence osGNS

namespace ChangingNomeCarrierNormalizedContinuumRoute

/-- Compile the explicit handoff to the standard same-object continuum
realization. -/
def toContinuumRealization
    {M : Nat → Type} {mu : ContinuumMeasure M}
    {existence : ContinuumYMExistence mu}
    {osGNS : MeasureLinkedOSGNSData existence}
    (route : ChangingNomeCarrierNormalizedContinuumRoute existence osGNS) :
    PhysicalSeparatorContinuumRealization
      (DynamicVacuumSectorObservablePin.exactCertificate
        route.observable.toObservablePin
        route.observable.cofinal.toPhysicalRateBand route.ceiling) mu :=
  route.handoff.toContinuumRealization

/-- Export the conditional continuum Yang--Mills exact-log-gap endpoint. -/
def toContinuumYMWithExactLogGap
    {M : Nat → Type} {mu : ContinuumMeasure M}
    {existence : ContinuumYMExistence mu}
    {osGNS : MeasureLinkedOSGNSData existence}
    (route : ChangingNomeCarrierNormalizedContinuumRoute existence osGNS) :
    ContinuumYMWithExactLogGap
      (DynamicVacuumSectorObservablePin.exactCertificate
        route.observable.toObservablePin
        route.observable.cofinal.toPhysicalRateBand route.ceiling) mu :=
  route.handoff.toContinuumYMWithExactLogGap

/-- The exact handoff retains a positive endpoint mass, conditionally on the
explicit reconstruction and rate inputs carried by the route. -/
theorem continuumMass_posEv
    {M : Nat → Type} {mu : ContinuumMeasure M}
    {existence : ContinuumYMExistence mu}
    {osGNS : MeasureLinkedOSGNSData existence}
    (route : ChangingNomeCarrierNormalizedContinuumRoute existence osGNS) :
    TuranPositivity.PosEv
      (PhysicalSeparatorContinuumRealization.endpointMass
        route.toContinuumYMWithExactLogGap) :=
  route.handoff.continuumMass_posEv

end ChangingNomeCarrierNormalizedContinuumRoute

end YMGap.Continuum.BF4PhysicalChangingNomeContinuumRoute

#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeContinuumRoute.ChangingNomeCarrierNormalizedContinuumRoute.toContinuumRealization
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeContinuumRoute.ChangingNomeCarrierNormalizedContinuumRoute.toContinuumYMWithExactLogGap
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeContinuumRoute.ChangingNomeCarrierNormalizedContinuumRoute.continuumMass_posEv
