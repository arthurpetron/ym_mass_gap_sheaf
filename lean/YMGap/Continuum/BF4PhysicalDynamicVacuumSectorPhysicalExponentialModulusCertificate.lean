/-
# Explicit-modulus refinement of the physical-exponential certificate

`BF4PhysicalDynamicVacuumSectorPhysicalExponentialCertificate` already
contracts the same-object observable, scheduled rate-power limit, and the two
Euler endpoint convergence propositions.  The endpoint propositions retain
their threshold in `Prop`; the constructive continuum law needs those
thresholds as data.  This module adds exactly that missing payload while
reusing the checked certificate unchanged.

The refinement is intentionally an input interface.  It does not extract a
modulus from a legacy `ConvergesTo` proof, choose a cutoff, or assert that the
dynamic physical-gap variation exists.  Its constructor asks for explicit
endpoint certificates on the same completed family and then packages them
with the existing forward/backward contraction.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Constructive.CRealConvergenceCertificate
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalExponentialCertificate

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalExponentialModulusCertificate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalExponentialCertificate
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerEulerCorridor
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerPhysicalExponentialCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeRationalVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler
open YMGap.Continuum.SummableRationalStepVariation

/-! ## Same-family endpoint moduli -/

/-- The physical-exponential certificate with explicit Type-level moduli for
both rational Euler endpoint streams.  The fields are indexed by the exact
`ratePower.limitRepresentative` retained by the base certificate, so a later
cutoff/spacing passage cannot silently substitute a different limit. -/
structure NormalizedMovingCubePhysicalExponentialModulusCertificate
    (family : DynamicVacuumSectorCompletedFamily 0) : Type 2 where
  certificate : NormalizedMovingCubePhysicalExponentialCertificate family
  upperModulus : ∀ time : Nat,
    CReal.ExplicitConvergenceCertificate
      (fun scale => scheduledSquaredRateUpperExponential
        family scale time)
      (certificate.ratePower.limitRepresentative time)
  lowerModulus : ∀ time : Nat,
    CReal.ExplicitConvergenceCertificate
      (fun scale => scheduledSquaredRateLowerExponential
        family certificate.ratePos scale time)
      (certificate.ratePower.limitRepresentative time)

namespace NormalizedMovingCubePhysicalExponentialModulusCertificate

/-- The explicit endpoint witnesses project to the legacy convergence fields
without recovering any erased witness by choice. -/
theorem upperConverges
    {family : DynamicVacuumSectorCompletedFamily 0}
    (data : NormalizedMovingCubePhysicalExponentialModulusCertificate family)
    (time : Nat) :
    CReal.ConvergesTo
      (fun scale => scheduledSquaredRateUpperExponential
        family scale time)
      (data.certificate.ratePower.limitRepresentative time) :=
  (data.upperModulus time).toConvergesTo

theorem lowerConverges
    {family : DynamicVacuumSectorCompletedFamily 0}
    (data : NormalizedMovingCubePhysicalExponentialModulusCertificate family)
    (time : Nat) :
    CReal.ConvergesTo
      (fun scale => scheduledSquaredRateLowerExponential
        family data.certificate.ratePos scale time)
      (data.certificate.ratePower.limitRepresentative time) :=
  (data.lowerModulus time).toConvergesTo

/-! ## Forward/backward constructor -/

/-- Add explicit endpoint moduli to the existing same-object contraction.
The rate-variation and rate-power producers remain explicit inputs to the
base constructor; this theorem does not manufacture them. -/
def ofRationalVariations
    (family : DynamicVacuumSectorCompletedFamily 0)
    (raw : MovingCubeRawScheduledRepresentativeVariation family)
    (normDebt : MovingCubeNormalizationNormDebtRationalVariation family)
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (rate_pos : ∀ scale,
      (0 : Q') < (family.completedGap scale).rate)
    (gapVariation : SummableRationalStepVariation family.physicalGap)
    (ratePower : NormalizedMovingCubeSampledRatePowerRationalVariation family)
    (upperModulus : ∀ time : Nat,
      CReal.ExplicitConvergenceCertificate
        (fun scale => scheduledSquaredRateUpperExponential
          family scale time)
        ((normalizedMovingCubePhysicalExponentialLimit family ratePower).limitRepresentative
          time))
    (lowerModulus : ∀ time : Nat,
      CReal.ExplicitConvergenceCertificate
        (fun scale => scheduledSquaredRateLowerExponential
          family rate_pos scale time)
        ((normalizedMovingCubePhysicalExponentialLimit family ratePower).limitRepresentative
          time)) :
    NormalizedMovingCubePhysicalExponentialModulusCertificate family where
  certificate :=
    NormalizedMovingCubePhysicalExponentialCertificate.ofRationalVariations
      family raw normDebt band rate_pos gapVariation ratePower
  upperModulus := upperModulus
  lowerModulus := lowerModulus

end NormalizedMovingCubePhysicalExponentialModulusCertificate

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalExponentialModulusCertificate

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalExponentialModulusCertificate.NormalizedMovingCubePhysicalExponentialModulusCertificate.upperConverges
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalExponentialModulusCertificate.NormalizedMovingCubePhysicalExponentialModulusCertificate.lowerConverges
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalExponentialModulusCertificate.NormalizedMovingCubePhysicalExponentialModulusCertificate.ofRationalVariations
