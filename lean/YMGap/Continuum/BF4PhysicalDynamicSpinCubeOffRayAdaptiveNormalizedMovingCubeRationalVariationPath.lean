/-
# Adaptive producer through the three rationalized variation frontiers

The dynamic adaptive transition-product family already produces the completed
transfer and the literal normalized moving-cube observable at every cutoff.
This file keeps that one producer index while exposing the three independent
cross-cutoff inputs required by its continuum connected-correlation path:

1. genuine `CReal` variation of raw same-object moment representatives;
2. rational variation of the reciprocal-square normalization debt; and
3. rational variation of the scheduled squared-rate power at positive times.

The time-zero rate branch is compiled automatically.  The three branches then
rejoin, for the same adaptive family and the same normalized observable, in a
strictly nonzero continuum channel and its squared-decay theorem.
Alternatively, the debt branch is compiled from variation of the reciprocal
scale plus one positive uniform ceiling, making the normalization fork
explicit without changing the observable lineage.

No cross-scale variation estimate or adaptive family is inhabited here.  In
particular this file does not prove a physical-exponential identification,
projective measure, OS reconstruction, continuum Yang--Mills theory, or Clay
conclusion.  No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubePath
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeRationalVariationCompiler

namespace YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeRationalVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler
open YMGap.Continuum.SummableRationalStepVariation

namespace DynamicSpinCubeOffRayAdaptiveTransitionProductFamily

/-! ## 1. Three parallel, producer-indexed frontier inputs -/

/-- Raw representative variation for the exact moving-cube moment stream of
this adaptive producer.  This branch remains genuinely constructive-real. -/
def MovingCubeRawVariation
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily) : Type 1 :=
  MovingCubeRawScheduledRepresentativeVariation family.toCompletedFamily

/-- Rational reciprocal-square normalization-debt variation for the exact
normalized moving cube of this adaptive producer. -/
def MovingCubeNormalizationDebtRationalVariation
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily) : Type 1 :=
  MovingCubeNormalizationNormDebtRationalVariation family.toCompletedFamily

/-- Rational variation of the reciprocal normalization scale before its norm-
debt square is formed. -/
def MovingCubeNormalizationScaleRationalVariation
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily) : Type 1 :=
  BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeRationalVariationCompiler.MovingCubeNormalizationScaleRationalVariation
    family.toCompletedFamily

/-- Scale variation plus a positive uniform reciprocal ceiling compiles to the
exact reciprocal-square normalization-debt variation for this producer. -/
def movingCubeNormalizationDebtRationalVariationOfScale
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (scaleVariation : MovingCubeNormalizationScaleRationalVariation family)
    (ceiling : Q') (ceiling_pos : (0 : Q') < ceiling)
    (scale_le_ceiling : forall scale,
      movingCubeNormalizationScale family.toCompletedFamily scale <= ceiling) :
    MovingCubeNormalizationDebtRationalVariation family :=
  movingCubeNormalizationNormDebtRationalVariationOfScale
    family.toCompletedFamily scaleVariation ceiling ceiling_pos
    scale_le_ceiling

/-- Positive-time rational rate-power variation for the exact physical-time
sampling schedule and completed rate of this adaptive producer. -/
def PositiveMovingCubeRatePowerRationalVariation
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily) : Type 1 :=
  forall time, 0 < time ->
    SummableRationalStepVariation
      (fun scale => normalizedMovingCubeSampledRatePower
        family.toCompletedFamily scale time)

/-! ## 2. Close time zero and rejoin the parallel branches -/

/-- Positive-time rate variation plus the definitional time-zero branch gives
the all-time rate-power certificate required by the continuum decay compiler. -/
def movingCubeRatePowerRationalVariationOfPositive
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family) :
    NormalizedMovingCubeSampledRatePowerRationalVariation
      family.toCompletedFamily :=
  normalizedMovingCubeSampledRatePowerRationalVariationOfPositive
    family.toCompletedFamily positiveRatePower

/-- The raw and normalization-debt branches compile to the continuum limit of
the literal normalized moving-cube connected correlation from this producer. -/
def normalizedMovingCubeContinuumLimitOfRationalVariations
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (raw : MovingCubeRawVariation family)
    (normalizationDebt : MovingCubeNormalizationDebtRationalVariation family) :
    BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubePath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.NormalizedMovingCubeContinuumLimit
      family :=
  normalizedMovingCubeLimitOfRationalDebtVariation family.toCompletedFamily
    raw normalizationDebt

/-- The rejoined same-observable continuum channel is strictly nonzero at
time zero. -/
theorem normalizedMovingCubeContinuumLimitOfRationalVariations_zero_isPositive
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (raw : MovingCubeRawVariation family)
    (normalizationDebt : MovingCubeNormalizationDebtRationalVariation family) :
    RCStrictPositivity.RCIsPositive
      (BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubePath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeContinuumConnectedAutocorrelation
        (normalizedMovingCubeContinuumLimitOfRationalVariations
          family raw normalizationDebt) 0) :=
  normalizedMovingCubeLimitOfRationalDebtVariation_zero_isPositive
    family.toCompletedFamily raw normalizationDebt

/-! ## 3. Rejoin through the smaller normalization-scale frontier -/

/-- The raw moment and bounded reciprocal-scale variation construct the exact
continuum limit without asking for squared-debt variation separately. -/
def normalizedMovingCubeContinuumLimitOfScaleRationalVariation
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (raw : MovingCubeRawVariation family)
    (scaleVariation : MovingCubeNormalizationScaleRationalVariation family)
    (ceiling : Q') (ceiling_pos : (0 : Q') < ceiling)
    (scale_le_ceiling : forall scale,
      movingCubeNormalizationScale family.toCompletedFamily scale <= ceiling) :
    BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubePath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.NormalizedMovingCubeContinuumLimit
      family :=
  normalizedMovingCubeContinuumLimitOfRationalVariations family raw
    (movingCubeNormalizationDebtRationalVariationOfScale family
      scaleVariation ceiling ceiling_pos scale_le_ceiling)

/-- The scale-variation route retains strict zero-time positivity of the same
normalized producer-connected continuum correlation. -/
theorem normalizedMovingCubeContinuumLimitOfScaleRationalVariation_zero_isPositive
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (raw : MovingCubeRawVariation family)
    (scaleVariation : MovingCubeNormalizationScaleRationalVariation family)
    (ceiling : Q') (ceiling_pos : (0 : Q') < ceiling)
    (scale_le_ceiling : forall scale,
      movingCubeNormalizationScale family.toCompletedFamily scale <= ceiling) :
    RCStrictPositivity.RCIsPositive
      (BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubePath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeContinuumConnectedAutocorrelation
        (normalizedMovingCubeContinuumLimitOfScaleRationalVariation family raw
          scaleVariation ceiling ceiling_pos scale_le_ceiling) 0) :=
  normalizedMovingCubeContinuumLimitOfRationalVariations_zero_isPositive
    family raw
    (movingCubeNormalizationDebtRationalVariationOfScale family
      scaleVariation ceiling ceiling_pos scale_le_ceiling)

/-- The three independently provable frontier branches reconverge in one
continuum squared-decay theorem for the actual adaptive-producer observable. -/
theorem normalizedMovingCubeContinuumLimitOfRationalVariations_sq_decay
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (raw : MovingCubeRawVariation family)
    (normalizationDebt : MovingCubeNormalizationDebtRationalVariation family)
    (positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family)
    (time : Nat) :
    CReal.RCle
      (CReal.RCmul
        (BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubePath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeContinuumConnectedAutocorrelation
          (normalizedMovingCubeContinuumLimitOfRationalVariations
            family raw normalizationDebt) time)
        (BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubePath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeContinuumConnectedAutocorrelation
          (normalizedMovingCubeContinuumLimitOfRationalVariations
            family raw normalizationDebt) time))
      (CReal.RCmul
        (CReal.RCmul
          (Quotient.mk CReal.crealSetoid
            ((BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler.normalizedMovingCubeSampledRatePowerLimitOfVariation
              family.toCompletedFamily
              (normalizedMovingCubeSampledRatePowerVariationOfRational
                family.toCompletedFamily
                (movingCubeRatePowerRationalVariationOfPositive
                  family positiveRatePower))).limitRepresentative
              time))
          (BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubePath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeContinuumConnectedAutocorrelation
            (normalizedMovingCubeContinuumLimitOfRationalVariations
              family raw normalizationDebt) 0))
        (BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubePath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeContinuumConnectedAutocorrelation
          (normalizedMovingCubeContinuumLimitOfRationalVariations
            family raw normalizationDebt) 0)) :=
  normalizedMovingCubeLimitOfRationalVariations_sq_decay
    family.toCompletedFamily raw normalizationDebt
    (movingCubeRatePowerRationalVariationOfPositive family positiveRatePower) time

/-- The smaller bounded-scale normalization route and the positive-time rate
branch reconverge in the same continuum squared-decay theorem. -/
theorem normalizedMovingCubeContinuumLimitOfScaleRationalVariation_sq_decay
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (raw : MovingCubeRawVariation family)
    (scaleVariation : MovingCubeNormalizationScaleRationalVariation family)
    (ceiling : Q') (ceiling_pos : (0 : Q') < ceiling)
    (scale_le_ceiling : forall scale,
      movingCubeNormalizationScale family.toCompletedFamily scale <= ceiling)
    (positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family)
    (time : Nat) :
    CReal.RCle
      (CReal.RCmul
        (BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubePath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeContinuumConnectedAutocorrelation
          (normalizedMovingCubeContinuumLimitOfScaleRationalVariation family raw
            scaleVariation ceiling ceiling_pos scale_le_ceiling) time)
        (BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubePath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeContinuumConnectedAutocorrelation
          (normalizedMovingCubeContinuumLimitOfScaleRationalVariation family raw
            scaleVariation ceiling ceiling_pos scale_le_ceiling) time))
      (CReal.RCmul
        (CReal.RCmul
          (Quotient.mk CReal.crealSetoid
            ((BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler.normalizedMovingCubeSampledRatePowerLimitOfVariation
              family.toCompletedFamily
              (normalizedMovingCubeSampledRatePowerVariationOfRational
                family.toCompletedFamily
                (movingCubeRatePowerRationalVariationOfPositive
                  family positiveRatePower))).limitRepresentative
              time))
          (BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubePath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeContinuumConnectedAutocorrelation
            (normalizedMovingCubeContinuumLimitOfScaleRationalVariation family raw
              scaleVariation ceiling ceiling_pos scale_le_ceiling) 0))
        (BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubePath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeContinuumConnectedAutocorrelation
          (normalizedMovingCubeContinuumLimitOfScaleRationalVariation family raw
            scaleVariation ceiling ceiling_pos scale_le_ceiling) 0)) :=
  normalizedMovingCubeContinuumLimitOfRationalVariations_sq_decay family raw
    (movingCubeNormalizationDebtRationalVariationOfScale family
      scaleVariation ceiling ceiling_pos scale_le_ceiling)
    positiveRatePower time

end DynamicSpinCubeOffRayAdaptiveTransitionProductFamily

end YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.movingCubeRatePowerRationalVariationOfPositive
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.movingCubeNormalizationDebtRationalVariationOfScale
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeContinuumLimitOfRationalVariations
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeContinuumLimitOfRationalVariations_zero_isPositive
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeContinuumLimitOfRationalVariations_sq_decay
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeContinuumLimitOfScaleRationalVariation_zero_isPositive
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubeContinuumLimitOfScaleRationalVariation_sq_decay
