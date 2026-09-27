/-
# Join the repaired carrier calibration to the normalized continuum route

This module records the exact same-family meeting point between the B04
cofinal-prefix calibration and the A05 variation/continuum compilers.  The
join is deliberately a certificate type rather than an inhabitant: its four
fields are the remaining analytic inputs.  Once supplied, the downstream
objects are definitionally tied to the repaired changing-nome completed
family, the normalized moving-cube observable, and the exact scheduled rate
factor.

No asymptotic witness, physical-exponential identification, OS reconstruction,
continuum Yang--Mills theory, or Clay conclusion is asserted here.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalChangingNomeExplicitMarginLaw
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeRationalVariationCompiler
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeGeometricClustering
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalExponentialCertificate

namespace YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalChangingNomeExplicitMarginLaw
open YMGap.Continuum.BF4PhysicalChangingNomeDynamicFamily
open YMGap.Continuum.BF4PhysicalCubeCutoffUniformGap
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeGeometricClustering
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeRationalVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalExponentialCertificate
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel
open YMGap.Continuum.RCStrictPositivity
open YMGap.Continuum.SummableRationalStepVariation

/-! ## The four-input meeting point -/

/-- Raw same-observable representative variation for the repaired family. -/
def RawVariation : Type 1 :=
  MovingCubeRawScheduledRepresentativeVariation
    changingNomeCarrierNormalizedDynamicFamily

/-- Rational reciprocal-square normalization-debt variation for the repaired
family. -/
def NormDebtVariation : Type 1 :=
  MovingCubeNormalizationNormDebtRationalVariation
    changingNomeCarrierNormalizedDynamicFamily

/-- Rational variation of the exact scheduled squared-rate power for the
repaired family. -/
def RatePowerVariation : Type 1 :=
  NormalizedMovingCubeSampledRatePowerRationalVariation
    changingNomeCarrierNormalizedDynamicFamily

/-- The honest typed join of the B04 calibration and the A05 same-observable
variation inputs.  It is intentionally not inhabited in the current
development. -/
structure Join : Type 1 where
  calibration : ChangingNomeCarrierNormalizedCofinalGapCalibration
  raw : RawVariation
  normDebt : NormDebtVariation
  ratePower : RatePowerVariation

/-! ## Exact downstream compilations -/

/-- The cofinal calibration gives the all-scale physical rate band on the
identical repaired completed family. -/
def Join.toPhysicalRateBand (data : Join) :
    DynamicVacuumSectorPhysicalRateBand
      changingNomeCarrierNormalizedDynamicFamily :=
  data.calibration.toPhysicalRateBand

/-- The raw and normalization-debt streams give the normalized continuum
same-observable RC limit. -/
def Join.toContinuumLimit (data : Join) :
    NormalizedMovingCubeScheduledRCContinuumLimit
      changingNomeCarrierNormalizedDynamicFamily :=
  normalizedMovingCubeLimitOfRationalDebtVariation
    changingNomeCarrierNormalizedDynamicFamily data.raw data.normDebt

/-- The scheduled-rate variation gives the exact constructive-real limit of the
finite squared-rate factor, without identifying it with a physical exponential.
-/
def Join.toRatePowerLimit (data : Join) :
    NormalizedMovingCubeSampledRatePowerLimit
      changingNomeCarrierNormalizedDynamicFamily :=
  normalizedMovingCubeSampledRatePowerLimitOfVariation
    changingNomeCarrierNormalizedDynamicFamily
    (normalizedMovingCubeSampledRatePowerVariationOfRational
      changingNomeCarrierNormalizedDynamicFamily data.ratePower)

/-- The scalar physical-gap interface produced by the joined calibration. -/
def Join.toContinuumGapTheorem (data : Join) :
    SharpContinuumObligation.ContinuumGapTheorem :=
  data.toPhysicalRateBand.toContinuumGapTheorem

/-! ## Rejoined consequences -/

theorem Join.zero_isPositive (data : Join) :
    RCIsPositive
      (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
        data.toContinuumLimit 0) :=
  normalizedMovingCubeLimitOfRationalDebtVariation_zero_isPositive
    changingNomeCarrierNormalizedDynamicFamily data.raw data.normDebt

/-- The normalized unit floor survives the joined cutoff limit.  This is
stronger than mere positivity: once the four-input join is supplied, the
same-object continuum response at time zero is at least one in the exact
constructive-real order. -/
theorem Join.zero_floor (data : Join) :
    CReal.RCle
      (Quotient.mk CReal.crealSetoid (CReal.ofQ' 1))
      (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
        data.toContinuumLimit 0) :=
  NormalizedMovingCubeScheduledRCContinuumLimit.one_le_continuumConnectedAutocorrelation_zero
    data.toContinuumLimit

/-- The joined same-object limit and exact scheduled rate-power limit form the
direct rate-power clustering contract.  This retains the actual CReal rate
stream and does not identify it with a fixed rational ratio or a physical
exponential. -/
def Join.toRatePowerClustering (data : Join) :
    NontrivialRCSquaredRatePowerClustering
      (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
        data.toContinuumLimit) :=
  NormalizedMovingCubeContinuumCertificate.toNontrivialRCSquaredRatePowerClusteringOfLimits
    changingNomeCarrierNormalizedDynamicFamily
    data.toContinuumLimit data.toRatePowerLimit

/-! ## The next physical-exponential handoff -/

/-- The repaired completed family has a strictly positive finite transfer rate
at every scale.  This is a finite-family fact; it is not a uniform physical
mass bound. -/
theorem carrierNormalized_rate_pos (scale : Nat) :
    (0 : Q') <
      (changingNomeCarrierNormalizedDynamicFamily.completedGap scale).rate := by
  rw [changingNomeCarrierNormalizedDynamicFamily_same_gap_rate]
  exact cutoffUniformRate_pos (changingNome scale)
    (Q'.le_of_lt (changingNome_pos scale))

/-- The physical-exponential corridor needs one additional exact variation
certificate: consecutive-scale variation of the same family's physical gap.
The existing `Join` supplies every other field, so this structure isolates the
remaining analytic input without weakening its identity. -/
structure PhysicalExponentialJoin : Type 1 where
  core : Join
  gapVariation : SummableRationalStepVariation
    changingNomeCarrierNormalizedDynamicFamily.physicalGap

/-- Compile the repaired-family join plus the single physical-gap variation
input into the existing same-object physical-exponential certificate. -/
def PhysicalExponentialJoin.toCertificate
    (data : PhysicalExponentialJoin) :
    NormalizedMovingCubePhysicalExponentialCertificate
      changingNomeCarrierNormalizedDynamicFamily :=
  NormalizedMovingCubePhysicalExponentialCertificate.ofRationalVariations
    changingNomeCarrierNormalizedDynamicFamily
    data.core.raw data.core.normDebt
    data.core.toPhysicalRateBand
    carrierNormalized_rate_pos
    data.gapVariation
    data.core.ratePower

theorem Join.sq_decay (data : Join) (time : Nat) :
    CReal.RCle
      (CReal.RCmul
        (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
          data.toContinuumLimit time)
        (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
          data.toContinuumLimit time))
      (CReal.RCmul
        (CReal.RCmul
          (Quotient.mk CReal.crealSetoid
            (data.toRatePowerLimit.limitRepresentative time))
          (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
            data.toContinuumLimit 0))
        (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
          data.toContinuumLimit 0)) :=
  normalizedMovingCubeLimitOfRationalVariations_sq_decay
    changingNomeCarrierNormalizedDynamicFamily data.raw data.normDebt
    data.ratePower time

end YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.Join.toPhysicalRateBand
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.Join.toContinuumLimit
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.Join.toRatePowerLimit
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.Join.toContinuumGapTheorem
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.Join.zero_isPositive
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.Join.zero_floor
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.Join.toRatePowerClustering
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.carrierNormalized_rate_pos
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.PhysicalExponentialJoin.toCertificate
#print axioms
  YMGap.Continuum.BF4PhysicalChangingNomeCarrierNormalizedContinuumJoin.Join.sq_decay
