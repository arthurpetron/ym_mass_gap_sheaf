/-
# Adaptive BF4 producer through the physical-exponential compiler

This module specializes the route-specific physical exponential to the exact
dynamic off-ray adaptive transition-product family.  It retains one strength
band, one physical-gap variation, and one scheduled-power variation on the
same completed family.  The positive physical-gap floor, the `2*M*t`
exponent, both rational exponential endpoints, and the normalized moving-cube
continuum decay consequently share one producer index.

No adaptive family, variation estimate, raw moment, normalization control,
projective measure, OS reconstruction, completed all-vector gap, continuum
Yang--Mills theory, or Clay conclusion is inhabited here.  No `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, or noncomputable declaration
is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerPhysicalExponentialCompiler

namespace YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptivePhysicalExponentialPath

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubePath
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubePath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeRationalVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerEulerCorridor
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerPhysicalExponentialCompiler
open YMGap.Continuum.SummableRationalStepVariation
open YMGap.Continuum.TuranPositivity

namespace DynamicSpinCubeOffRayAdaptiveTransitionProductFamily

/-! ## 1. Producer-indexed physical mass and exponential data -/

/-- Summable rational variation of the exact physical gap of this adaptive
producer. -/
def PhysicalGapRationalVariation
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily) : Type 1 :=
  SummableRationalStepVariation family.toCompletedFamily.physicalGap

/-- The same strength band that controls the completed transfer gives the
explicit positive floor of the selected physical-gap limit. -/
theorem physicalGapVariationLimit_floor
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (band : family.StrengthBand)
    (gapVariation : PhysicalGapRationalVariation family) :
    CReal.leEv
      (CReal.ofQ' (family.physicalRateBand band).floor)
      gapVariation.limit :=
  BF4PhysicalDynamicVacuumSectorScheduledRatePowerPhysicalExponentialCompiler.physicalGapVariationLimit_floor
    family.toCompletedFamily (family.physicalRateBand band) gapVariation

/-- The selected physical mass of the adaptive producer is strictly positive. -/
theorem physicalGapVariationLimit_posEv
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (band : family.StrengthBand)
    (gapVariation : PhysicalGapRationalVariation family) :
    PosEv gapVariation.limit :=
  BF4PhysicalDynamicVacuumSectorScheduledRatePowerPhysicalExponentialCompiler.physicalGapVariationLimit_posEv
    family.toCompletedFamily (family.physicalRateBand band) gapVariation

/-- The common scheduled exponent of the adaptive producer is positive at
every positive physical time. -/
theorem scheduledSquaredRatePhysicalExponentLimit_posEv
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (band : family.StrengthBand)
    (gapVariation : PhysicalGapRationalVariation family)
    (time : Nat) (time_pos : 0 < time) :
    PosEv
      (BF4PhysicalDynamicVacuumSectorScheduledRatePowerExponentLimitCompiler.scheduledSquaredRatePhysicalExponentLimit
        gapVariation time) :=
  BF4PhysicalDynamicVacuumSectorScheduledRatePowerPhysicalExponentialCompiler.scheduledSquaredRatePhysicalExponentLimit_posEv
    family.toCompletedFamily (family.physicalRateBand band) gapVariation
    time time_pos

/-- The exact all-time scheduled-power limit obtained from the positive-time
variation input already used by the adaptive normalized observable path. -/
def physicalExponentialLimit
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family) :
    NormalizedMovingCubeSampledRatePowerLimit family.toCompletedFamily :=
  normalizedMovingCubePhysicalExponentialLimit family.toCompletedFamily
    (movingCubeRatePowerRationalVariationOfPositive
      family positiveRatePower)

/-- Both Euler exponential endpoints converge to the exact rate factor used
by this adaptive producer's normalized moving-cube decay theorem. -/
theorem physicalExponentialLimit_identification
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (band : family.StrengthBand)
    (gapVariation : PhysicalGapRationalVariation family)
    (positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family)
    (time : Nat) :
    CReal.ConvergesTo
        (fun scale => scheduledSquaredRateUpperExponential
          family.toCompletedFamily scale time)
        ((physicalExponentialLimit family positiveRatePower).limitRepresentative
          time) /\
      CReal.ConvergesTo
        (fun scale => scheduledSquaredRateLowerExponential
          family.toCompletedFamily
          (BF4PhysicalDynamicVacuumSectorScheduledRatePowerEulerCorridor.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.completedRate_pos
            family)
          scale time)
        ((physicalExponentialLimit family positiveRatePower).limitRepresentative
          time) := by
  exact normalizedMovingCubePhysicalExponentialLimit_identification
    family.toCompletedFamily (family.physicalRateBand band)
    (BF4PhysicalDynamicVacuumSectorScheduledRatePowerEulerCorridor.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.completedRate_pos
      family)
    gapVariation
    (movingCubeRatePowerRationalVariationOfPositive
      family positiveRatePower)
    time

/-! ## 2. Rejoin the physical exponential with the same observable -/

/-- The adaptive same-observable continuum decay and both physical-
exponential endpoint identifications are returned together.  The rate limit
in the inequality is definitionally `physicalExponentialLimit`. -/
theorem normalizedMovingCubePhysicalExponential_sq_decay
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (raw : MovingCubeRawVariation family)
    (normalizationDebt : MovingCubeNormalizationDebtRationalVariation family)
    (band : family.StrengthBand)
    (gapVariation : PhysicalGapRationalVariation family)
    (positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family)
    (time : Nat) :
    CReal.RCle
        (CReal.RCmul
          (normalizedMovingCubeContinuumConnectedAutocorrelation
            (normalizedMovingCubeContinuumLimitOfRationalVariations
              family raw normalizationDebt) time)
          (normalizedMovingCubeContinuumConnectedAutocorrelation
            (normalizedMovingCubeContinuumLimitOfRationalVariations
              family raw normalizationDebt) time))
        (CReal.RCmul
          (CReal.RCmul
            (Quotient.mk CReal.crealSetoid
              ((physicalExponentialLimit family positiveRatePower).limitRepresentative
                time))
            (normalizedMovingCubeContinuumConnectedAutocorrelation
              (normalizedMovingCubeContinuumLimitOfRationalVariations
                family raw normalizationDebt) 0))
          (normalizedMovingCubeContinuumConnectedAutocorrelation
            (normalizedMovingCubeContinuumLimitOfRationalVariations
              family raw normalizationDebt) 0)) /\
      (CReal.ConvergesTo
          (fun scale => scheduledSquaredRateUpperExponential
            family.toCompletedFamily scale time)
          ((physicalExponentialLimit family positiveRatePower).limitRepresentative
            time) /\
        CReal.ConvergesTo
          (fun scale => scheduledSquaredRateLowerExponential
            family.toCompletedFamily
            (BF4PhysicalDynamicVacuumSectorScheduledRatePowerEulerCorridor.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.completedRate_pos
              family)
            scale time)
          ((physicalExponentialLimit family positiveRatePower).limitRepresentative
            time)) := by
  exact
    ⟨normalizedMovingCubeContinuumLimitOfRationalVariations_sq_decay
        family raw normalizationDebt positiveRatePower time,
      physicalExponentialLimit_identification
        family band gapVariation positiveRatePower time⟩

end DynamicSpinCubeOffRayAdaptiveTransitionProductFamily

end YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptivePhysicalExponentialPath

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptivePhysicalExponentialPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.physicalGapVariationLimit_floor
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptivePhysicalExponentialPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.physicalGapVariationLimit_posEv
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptivePhysicalExponentialPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.scheduledSquaredRatePhysicalExponentLimit_posEv
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptivePhysicalExponentialPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.physicalExponentialLimit
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptivePhysicalExponentialPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.physicalExponentialLimit_identification
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptivePhysicalExponentialPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubePhysicalExponential_sq_decay
