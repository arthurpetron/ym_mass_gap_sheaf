/-
# Adaptive raw observable through the physical exponential

This module specializes the normalization-free continuum decay compiler to
the exact dynamic off-ray adaptive transition-product producer.  The raw
moving-cube representative variation, its one zero-time nontriviality
certificate, the physical-gap variation, and the scheduled-power variation
all remain indexed by that single producer.

The final theorem returns, together:

* positivity of the raw observable's actual zero-time continuum limit;
* squared decay of that same raw continuum correlation with its own
  zero-time value as amplitude; and
* convergence of both Euler exponential endpoints to the exact rate factor
  occurring in the decay inequality.

No normalization-debt input occurs.  No adaptive family, raw variation,
zero-time nontriviality, physical-gap variation, scheduled-power variation,
projective measure, OS reconstruction, continuum Yang--Mills theory, or Clay
conclusion is inhabited here.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptivePhysicalExponentialPath
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeContinuumDecayCompiler

namespace YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawPhysicalExponentialPath

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptivePhysicalExponentialPath
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptivePhysicalExponentialPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerPhysicalExponentialCompiler
open YMGap.Continuum.RCStrictPositivity

namespace DynamicSpinCubeOffRayAdaptiveTransitionProductFamily

/-! ## 1. One adaptive producer, one raw observable -/

/-- The exact raw scheduled continuum limit selected by the adaptive
producer's same-object moving-cube variation. -/
def rawMovingCubeContinuumLimit
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (raw : MovingCubeRawVariation family) :=
  rawMovingCubeContinuumLimitOfVariation family.toCompletedFamily raw

/-- The remaining nontriviality obligation is indexed by the exact raw limit
above.  It asks only that this observable survive at time zero. -/
def RawMovingCubeContinuumNontriviality
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (raw : MovingCubeRawVariation family) : Type 1 :=
  MovingCubeRawContinuumNontriviality family.toCompletedFamily raw

/-- The raw continuum connected correlation retains the exact adaptive
producer and representative-variation lineage. -/
def rawMovingCubeContinuumConnectedAutocorrelation
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (raw : MovingCubeRawVariation family)
    (time : Nat) : CReal.RC :=
  (rawMovingCubeContinuumLimit family raw).continuumConnectedAutocorrelation
    time

/-! ## 2. Rejoin with the exact physical exponential -/

/-- The normalization-free adaptive path rejoins all of its inputs on one
observable.  In particular, the physical exponential in the inequality is
definitionally `physicalExponentialLimit`, and the amplitude is the same raw
correlation evaluated at time zero. -/
theorem rawMovingCubePhysicalExponentialPath
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (raw : MovingCubeRawVariation family)
    (nontrivial : RawMovingCubeContinuumNontriviality family raw)
    (band : family.StrengthBand)
    (gapVariation : PhysicalGapRationalVariation family)
    (positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family)
    (time : Nat) :
    RCIsPositive
        (rawMovingCubeContinuumConnectedAutocorrelation family raw 0) /\
      CReal.RCle
          (CReal.RCmul
            (rawMovingCubeContinuumConnectedAutocorrelation family raw time)
            (rawMovingCubeContinuumConnectedAutocorrelation family raw time))
          (CReal.RCmul
            (CReal.RCmul
              (Quotient.mk CReal.crealSetoid
                ((physicalExponentialLimit family
                  positiveRatePower).limitRepresentative time))
              (rawMovingCubeContinuumConnectedAutocorrelation family raw 0))
            (rawMovingCubeContinuumConnectedAutocorrelation family raw 0)) /\
        (CReal.ConvergesTo
            (fun scale => scheduledSquaredRateUpperExponential
              family.toCompletedFamily scale time)
            ((physicalExponentialLimit family
              positiveRatePower).limitRepresentative time) /\
          CReal.ConvergesTo
            (fun scale => scheduledSquaredRateLowerExponential
              family.toCompletedFamily
              (BF4PhysicalDynamicVacuumSectorScheduledRatePowerEulerCorridor.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.completedRate_pos
                family)
              scale time)
            ((physicalExponentialLimit family
              positiveRatePower).limitRepresentative time)) := by
  have hraw := rawMovingCubeObservableConnectedContinuumPath
    family.toCompletedFamily raw nontrivial
    (physicalExponentialLimit family positiveRatePower) time
  exact
    ⟨hraw.1, hraw.2,
      physicalExponentialLimit_identification
        family band gapVariation positiveRatePower time⟩

end DynamicSpinCubeOffRayAdaptiveTransitionProductFamily

end YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawPhysicalExponentialPath

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawPhysicalExponentialPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.rawMovingCubeContinuumLimit
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawPhysicalExponentialPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.rawMovingCubeContinuumConnectedAutocorrelation
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawPhysicalExponentialPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.rawMovingCubePhysicalExponentialPath
