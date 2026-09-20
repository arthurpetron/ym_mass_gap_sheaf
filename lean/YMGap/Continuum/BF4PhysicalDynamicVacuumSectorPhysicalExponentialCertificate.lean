/-
# Same-object physical-exponential certificate for the normalized moving-cube route

The constructive certificate rule requires more than a named limiting value:
the approximating observable, its CReal modulus, and the comparison estimates
must remain attached to one completed family.  The preceding compilers already
provide these pieces separately.  This module contracts them into one typed
certificate for the physical-exponential route:

* the normalized connected observable is the limit built from the supplied raw
  representative and normalization-debt variation;
* the scheduled rate-power limit is the exact same rate-power stream selected
  by the physical-exponential compiler;
* the squared decay and both rational Euler endpoint convergences are retained
  as fields, not replaced by an untyped assertion; and
* the direct CReal clustering consumer is applied to those two same-object
  limits, without imposing a fixed rational ratio.

This is a contraction of existing witnesses, not a new analytic producer.  It
does not inhabit raw/debt/rate variation, a cofinal cutoff family, a uniform
physical gap, thermodynamic or continuum descent, OS/QFT reconstruction,
all-group extension, or the Clay mass-gap theorem.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeGeometricClustering
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerPhysicalExponentialCompiler

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalExponentialCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeGeometricClustering
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeRationalVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerEulerCorridor
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerPhysicalExponentialCompiler
open YMGap.Continuum.SummableRationalStepVariation

/-! ## 1. The retained same-object certificate -/

/-- A physical-exponential certificate keeps the normalized continuum limit,
the exact scheduled CReal rate-power limit, the direct clustering witness, and
the endpoint comparison moduli in one dependent object.  The `sameObjectSqDecay`
field records the stronger rational-variation compiler output rather than
reconstructing it from an unrelated correlation stream. -/
structure NormalizedMovingCubePhysicalExponentialCertificate
    (family : DynamicVacuumSectorCompletedFamily 0) : Type 2 where
  limit : NormalizedMovingCubeScheduledRCContinuumLimit family
  ratePower : NormalizedMovingCubeSampledRatePowerLimit family
  clustering : NontrivialRCSquaredRatePowerClustering
    limit.continuumConnectedAutocorrelation
  ratePos : forall scale,
    (0 : Q') < (family.completedGap scale).rate
  sameObjectSqDecay : forall time : Nat,
    CReal.RCle
      (CReal.RCmul
        (limit.continuumConnectedAutocorrelation time)
        (limit.continuumConnectedAutocorrelation time))
      (CReal.RCmul
        (CReal.RCmul
          (Quotient.mk CReal.crealSetoid
            (ratePower.limitRepresentative time))
          (limit.continuumConnectedAutocorrelation 0))
        (limit.continuumConnectedAutocorrelation 0))
  upperConvergence : forall time : Nat,
    CReal.ConvergesTo
      (fun scale => scheduledSquaredRateUpperExponential
        family scale time)
      (ratePower.limitRepresentative time)
  lowerConvergence : forall time : Nat,
    CReal.ConvergesTo
      (fun scale => scheduledSquaredRateLowerExponential
        family ratePos scale time)
      (ratePower.limitRepresentative time)

/-! ## 2. Forward/backward contraction -/

/-- Join the explicit raw, normalization-debt, physical-gap, and scheduled
rate-power variation certificates.  Every output field is definitionally tied
to the same completed family and the same observable; no fixed-ratio shortcut
is introduced. -/
def NormalizedMovingCubePhysicalExponentialCertificate.ofRationalVariations
    (family : DynamicVacuumSectorCompletedFamily 0)
    (raw : MovingCubeRawScheduledRepresentativeVariation family)
    (normDebt : MovingCubeNormalizationNormDebtRationalVariation family)
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (rate_pos : forall scale,
      (0 : Q') < (family.completedGap scale).rate)
    (gapVariation : SummableRationalStepVariation family.physicalGap)
    (ratePower : NormalizedMovingCubeSampledRatePowerRationalVariation family) :
    NormalizedMovingCubePhysicalExponentialCertificate family where
  limit := normalizedMovingCubeLimitOfRationalDebtVariation
    family raw normDebt
  ratePower := normalizedMovingCubePhysicalExponentialLimit family ratePower
  clustering :=
    NormalizedMovingCubeContinuumCertificate.toNontrivialRCSquaredRatePowerClusteringOfLimits
      family
      (normalizedMovingCubeLimitOfRationalDebtVariation family raw normDebt)
      (normalizedMovingCubePhysicalExponentialLimit family ratePower)
  ratePos := rate_pos
  sameObjectSqDecay := by
    intro time
    exact (normalizedMovingCubePhysicalExponential_sq_decay
      family raw normDebt band rate_pos gapVariation ratePower time).1
  upperConvergence := by
    intro time
    exact (normalizedMovingCubePhysicalExponentialLimit_identification
      family band rate_pos gapVariation ratePower time).1
  lowerConvergence := by
    intro time
    exact (normalizedMovingCubePhysicalExponentialLimit_identification
      family band rate_pos gapVariation ratePower time).2

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalExponentialCertificate

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalExponentialCertificate.NormalizedMovingCubePhysicalExponentialCertificate.ofRationalVariations
