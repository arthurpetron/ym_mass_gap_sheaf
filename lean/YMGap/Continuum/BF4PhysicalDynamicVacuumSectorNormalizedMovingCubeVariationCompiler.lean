/-
# Three parallel scale-variation inputs for one continuum decay channel

The observable-connected normalized continuum frontier has three independent
cutoff-scale convergence streams:

1. representatives of the raw sampled moving-cube correlation;
2. the reciprocal-square normalization debt; and
3. the exact scheduled squared-rate power.

This file states each stream as a summable consecutive-scale variation and
constructs the corresponding `CReal` Cauchy modulus and limit.  The three
streams then rejoin through the already-proved product-limit and continuum-
decay compilers.  Thus parallel analytic work produces one nonzero continuum
same-observable decay channel, rather than three unrelated limit objects.

No variation estimate is inhabited here.  No physical-exponential
identification, adaptive producer, projective measure, OS reconstruction,
continuum Yang--Mills theory, or Clay conclusion is proved.  No `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, or noncomputable declaration is
used.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
import YMGap.Continuum.SummableCRealStepVariation

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeLimitCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel
open YMGap.Continuum.SummableCRealStepVariation

/-! ## 1. Raw same-observable representative variation -/

/-- Explicit representatives of the raw sampled moving-cube `RC` classes,
together with a summable consecutive-cutoff variation at every physical time.
The `represents` field prevents a smoother unrelated sequence from entering. -/
structure MovingCubeRawScheduledRepresentativeVariation
    (family : DynamicVacuumSectorCompletedFamily 0) : Type 1 where
  representative : Nat -> Nat -> CReal
  represents : forall time scale,
    Quotient.mk CReal.crealSetoid (representative time scale) =
      sampledConnectedAutocorrelation
        (centralPhysicalDynamicMovingCubeRCChannel family) scale time
  variation : forall time,
    SummableCRealStepVariation (fun scale => representative time scale)

namespace MovingCubeRawScheduledRepresentativeVariation

/-- Summable raw representative variation constructs the exact scheduled raw
same-observable cutoff limit. -/
def toScheduledRCContinuumLimit
    {family : DynamicVacuumSectorCompletedFamily 0}
    (data : MovingCubeRawScheduledRepresentativeVariation family) :
    ScheduledRCContinuumLimit
      (centralPhysicalDynamicMovingCubeRCChannel family) where
  representative := data.representative
  represents := data.represents
  limitRepresentative := fun time =>
    CReal.completeLimitCauchy
      (fun scale => data.representative time scale)
      (data.variation time).toModCauchyEv
  converges := fun time =>
    CReal.convergesTo_completeLimitCauchy
      (fun scale => data.representative time scale)
      (data.variation time).toModCauchyEv

end MovingCubeRawScheduledRepresentativeVariation

/-! ## 2. Normalization-debt variation -/

/-- A summable consecutive-cutoff estimate for the exact reciprocal-square
normalization debt. -/
def MovingCubeNormalizationNormDebtVariation
    (family : DynamicVacuumSectorCompletedFamily 0) : Type 1 :=
  SummableCRealStepVariation
    (fun scale => CReal.ofQ'
      (movingCubeNormalizationNormDebt family scale))

/-- Summable reciprocal-square debt variation constructs its exact
constructive-real cutoff limit. -/
def movingCubeNormalizationNormDebtLimitOfVariation
    (family : DynamicVacuumSectorCompletedFamily 0)
    (variation : MovingCubeNormalizationNormDebtVariation family) :
    MovingCubeNormalizationNormDebtLimit family where
  limitRepresentative :=
    CReal.completeLimitCauchy
      (fun scale => CReal.ofQ'
        (movingCubeNormalizationNormDebt family scale))
      variation.toModCauchyEv
  converges :=
    CReal.convergesTo_completeLimitCauchy
      (fun scale => CReal.ofQ'
        (movingCubeNormalizationNormDebt family scale))
      variation.toModCauchyEv

/-! ## 3. Scheduled rate-power variation -/

/-- Summable consecutive-cutoff estimates for the exact scheduled squared-rate
power at every integer physical time. -/
def NormalizedMovingCubeSampledRatePowerVariation
    (family : DynamicVacuumSectorCompletedFamily 0) : Type 1 :=
  forall time, SummableCRealStepVariation
    (fun scale => CReal.ofQ'
      (normalizedMovingCubeSampledRatePower family scale time))

/-- Summable scheduled rate-power variation constructs the exact rate-power
limit required by the continuum decay compiler. -/
def normalizedMovingCubeSampledRatePowerLimitOfVariation
    (family : DynamicVacuumSectorCompletedFamily 0)
    (variation : NormalizedMovingCubeSampledRatePowerVariation family) :
    NormalizedMovingCubeSampledRatePowerLimit family where
  limitRepresentative := fun time =>
    CReal.completeLimitCauchy
      (fun scale => CReal.ofQ'
        (normalizedMovingCubeSampledRatePower family scale time))
      (variation time).toModCauchyEv
  converges := fun time =>
    CReal.convergesTo_completeLimitCauchy
      (fun scale => CReal.ofQ'
        (normalizedMovingCubeSampledRatePower family scale time))
      (variation time).toModCauchyEv

/-! ## 4. Rejoin the parallel streams on one observable -/

/-- The normalized same-observable cutoff limit constructed from explicit raw
and normalization-debt variation streams. -/
def normalizedMovingCubeLimitOfVariations
    (family : DynamicVacuumSectorCompletedFamily 0)
    (raw : MovingCubeRawScheduledRepresentativeVariation family)
    (normDebt : MovingCubeNormalizationNormDebtVariation family) :
    NormalizedMovingCubeScheduledRCContinuumLimit family :=
  compileNormalizedMovingCubeScheduledRCContinuumLimit family
    raw.toScheduledRCContinuumLimit
    (movingCubeNormalizationNormDebtLimitOfVariation family normDebt)

/-- The raw and debt variation streams rejoin in a continuum channel that is
strictly positive at time zero. -/
theorem normalizedMovingCubeLimitOfVariations_zero_isPositive
    (family : DynamicVacuumSectorCompletedFamily 0)
    (raw : MovingCubeRawScheduledRepresentativeVariation family)
    (normDebt : MovingCubeNormalizationNormDebtVariation family) :
    RCStrictPositivity.RCIsPositive
      (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
        (normalizedMovingCubeLimitOfVariations family raw normDebt) 0) :=
  NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation_zero_isPositive
    (normalizedMovingCubeLimitOfVariations family raw normDebt)

/-- The three variation streams rejoin in the continuum squared-decay theorem
for the same normalized moving-cube observable. -/
theorem normalizedMovingCubeLimitOfVariations_sq_decay
    (family : DynamicVacuumSectorCompletedFamily 0)
    (raw : MovingCubeRawScheduledRepresentativeVariation family)
    (normDebt : MovingCubeNormalizationNormDebtVariation family)
    (ratePower : NormalizedMovingCubeSampledRatePowerVariation family)
    (time : Nat) :
    CReal.RCle
      (CReal.RCmul
        (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
          (normalizedMovingCubeLimitOfVariations family raw normDebt) time)
        (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
          (normalizedMovingCubeLimitOfVariations family raw normDebt) time))
      (CReal.RCmul
        (CReal.RCmul
          (Quotient.mk CReal.crealSetoid
            ((normalizedMovingCubeSampledRatePowerLimitOfVariation
              family ratePower).limitRepresentative time))
          (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
            (normalizedMovingCubeLimitOfVariations family raw normDebt) 0))
        (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
          (normalizedMovingCubeLimitOfVariations family raw normDebt) 0)) :=
  normalizedMovingCubeContinuumConnectedAutocorrelationSq_decay
    family (normalizedMovingCubeLimitOfVariations family raw normDebt)
    (normalizedMovingCubeSampledRatePowerLimitOfVariation family ratePower) time

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler.MovingCubeRawScheduledRepresentativeVariation.toScheduledRCContinuumLimit
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler.movingCubeNormalizationNormDebtLimitOfVariation
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler.normalizedMovingCubeSampledRatePowerLimitOfVariation
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler.normalizedMovingCubeLimitOfVariations_zero_isPositive
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler.normalizedMovingCubeLimitOfVariations_sq_decay
