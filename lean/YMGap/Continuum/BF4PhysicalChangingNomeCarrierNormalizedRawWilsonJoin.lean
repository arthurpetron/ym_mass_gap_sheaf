/-
# Same-carrier handoff from the repaired normalized join to the Wilson path

`ConcreteJoin` keeps the response floor, physical calibration, and all three
cutoff-variation streams on one repaired SU(2) family.  This module attaches
the existing raw Wilson/OS/GNS certificates to that same family and compiles
them to `RawWilsonConnectedMassGapPath`.  The constructor does not create any
OS/GNS, graph-norm, exact-rate, or vacuum-stationarity witness; it only makes
their precise same-carrier meeting point explicit.

No continuum Yang--Mills, physical-mass, every-group, or Clay conclusion is
asserted here.  No `Classical.*`, choice, `native_decide`, `sorry`, custom
axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin
import YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath

namespace YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedRawWilsonJoin

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin
open YMGap.Continuum.BF4PhysicalChangingNomeExplicitMarginLaw
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeNontrivialityCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeProjectiveOSCorrelationHandoff
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeWilsonGNSHandoff
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorWilsonExactRateHandoff
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorWilsonGraphNormLimitCompiler
open YMGap.Continuum.BF4PhysicalSelectedVacuumMeanConvergence
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalExponentialCertificate
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.SummableRationalStepVariation
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff
open YMGap.Continuum.WilsonIteratedNormDecayHandoff

/-! ## Same-family OS/GNS handoff inputs -/

/-- The Wilson/OS certificates for explicitly named repaired-family streams.
    Separating this bundle from `ConcreteJoin` avoids asking the elaborator to
    normalize every dependent projection at every field while retaining all
    same-carrier indices in the type. -/
structure WilsonCertificates
    (raw : MovingCubeRawScheduledRepresentativeVariation
      changingNomeCarrierNormalizedDynamicFamily)
    (gapVariation : SummableRationalStepVariation
      changingNomeCarrierNormalizedDynamicFamily.physicalGap)
    (ratePower : NormalizedMovingCubeSampledRatePowerLimit
      changingNomeCarrierNormalizedDynamicFamily)
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (H : ContinuumYMExistence mu)
    (W : WilsonSelectedOSGNSData H) : Type 3 where
  projectiveOS : RawMovingCubeProjectiveOSCorrelationHandoff
    changingNomeCarrierNormalizedDynamicFamily raw H W.measureLinked
  matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
    changingNomeCarrierNormalizedDynamicFamily raw H W projectiveOS
  exactRate : DynamicVacuumSectorWilsonExactRateHandoff
    changingNomeCarrierNormalizedDynamicFamily gapVariation W
  graphNorm : DynamicVacuumSectorWilsonPhysicalTimeGraphNormLimit
    changingNomeCarrierNormalizedDynamicFamily ratePower W
  vacuumPin : WilsonDenseUnitStationaryVacuumPin W

/-- All remaining raw Wilson-path inputs attached to one `ConcreteJoin`.
    The only dependent boundary is the named core projection; the certificate
    fields themselves are checked in the smaller `WilsonCertificates` bundle. -/
structure WilsonJoin
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (H : ContinuumYMExistence mu)
    (W : WilsonSelectedOSGNSData H) : Type 4 where
  core : ConcreteJoin
  gapVariation : SummableRationalStepVariation
    changingNomeCarrierNormalizedDynamicFamily.physicalGap
  certificates : WilsonCertificates core.raw gapVariation
    core.toRatePowerLimit H W

/-! ## Contraction to the existing raw Wilson path -/

/-- The same-family certificates compile to the existing Wilson connected
    mass-gap path, with nontriviality obtained from the transported response
    floor on the canonical moving-cube carrier. -/
def WilsonJoin.toPath
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (data : WilsonJoin H W) :
    RawWilsonConnectedMassGapPath
      changingNomeCarrierNormalizedDynamicFamily data.core.raw
      data.core.toJoin.toPhysicalRateBand data.gapVariation
    data.core.toRatePowerLimit H W :=
  RawWilsonConnectedMassGapPath.ofUniformNormFloor
    (family := changingNomeCarrierNormalizedDynamicFamily)
    (raw := data.core.raw)
    (band := data.core.toJoin.toPhysicalRateBand)
    (gapVariation := data.gapVariation)
    (ratePower := data.core.toRatePowerLimit)
    (uniform := data.core.toCanonicalUniformRCNormFloor)
    data.certificates.projectiveOS data.certificates.matrixCoefficient
    data.certificates.exactRate data.certificates.graphNorm
    data.certificates.vacuumPin

/-- The path's nontriviality field is the response-aware raw certificate
    selected by the same `ConcreteJoin`; no alternate observable is chosen. -/
def WilsonJoin.toPath_nontrivial
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (data : WilsonJoin H W) :
    MovingCubeRawContinuumNontriviality
      changingNomeCarrierNormalizedDynamicFamily data.core.raw :=
  data.toPath.nontrivial

/- The already-defined exact-rate and graph-norm contraction can now be
   consumed without losing the same repaired-family indices. -/
def WilsonJoin.toMinimalBoundedMassGap
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (data : WilsonJoin H W) :
    WilsonMinimalBoundedMassGap W :=
  data.toPath.minimalBoundedMassGap

/-- The same stationary-vacuum certificate upgrades the conditional minimal
    endpoint to the all-integer-iterate Wilson gap interface. -/
def WilsonJoin.toIteratedBoundedMassGap
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (data : WilsonJoin H W) :
    WilsonIteratedBoundedMassGap W :=
  data.toPath.iteratedBoundedMassGap

/-! ## Same-carrier physical-exponential handoff -/

/-- The Wilson join plus the one remaining physical-gap variation certificate.
    Keeping the Wilson data inside this bundle prevents the physical-
    exponential compiler from being paired with an unrelated repaired carrier. -/
structure WilsonPhysicalExponentialJoin
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (H : ContinuumYMExistence mu)
    (W : WilsonSelectedOSGNSData H) : Type 4 where
  wilson : WilsonJoin H W
  gapVariation : SummableRationalStepVariation
    changingNomeCarrierNormalizedDynamicFamily.physicalGap

/-- Repackage the same repaired-family physical-gap variation for the existing
    physical-exponential compiler.  The Wilson certificate remains available
    through `wilson`; no physical exponential is inferred from it. -/
def WilsonPhysicalExponentialJoin.toPhysicalExponentialJoin
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (data : WilsonPhysicalExponentialJoin H W) :
    PhysicalExponentialJoin :=
  { core := data.wilson.core.toJoin
    gapVariation := data.gapVariation }

/-- Compile the same-family physical-gap variation to the existing
    constructive physical-exponential certificate. -/
def WilsonPhysicalExponentialJoin.toCertificate
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (data : WilsonPhysicalExponentialJoin H W) :
    NormalizedMovingCubePhysicalExponentialCertificate
      changingNomeCarrierNormalizedDynamicFamily :=
  data.toPhysicalExponentialJoin.toCertificate

end YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedRawWilsonJoin

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedRawWilsonJoin.WilsonJoin.toPath
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedRawWilsonJoin.WilsonJoin.toPath_nontrivial
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedRawWilsonJoin.WilsonJoin.toMinimalBoundedMassGap
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedRawWilsonJoin.WilsonJoin.toIteratedBoundedMassGap
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedRawWilsonJoin.WilsonPhysicalExponentialJoin.toPhysicalExponentialJoin
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedRawWilsonJoin.WilsonPhysicalExponentialJoin.toCertificate
