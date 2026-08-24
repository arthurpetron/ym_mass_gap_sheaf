/-
# Rationalize the moving-cube debt and scheduled-rate variation frontiers

The reciprocal-square normalization debt and exact scheduled squared-rate
power are literal `Q'` streams.  Requiring arbitrary constructive-real step
data for them obscures the finite analytic target.  This file replaces those
two obligations by summable rational step budgets and compiles them through
the canonical `CReal.ofQ'` embedding.

The time-zero scheduled-rate stream is pointwise equivalent to one, so its
zero variation certificate is constructed unconditionally.  Consequently a
family of rational rate-power variations is reduced to positive physical
times only.  The raw sampled connected moment remains genuinely `CReal`; no
claim that it is rational is made.  The squared normalization debt can also be
compiled from variation of the reciprocal scale itself, provided one honest
uniform ceiling for that scale is supplied.

No positive-time rate variation, normalization-debt variation, raw moment
variation, adaptive producer, physical-exponential identification, projective
measure, OS reconstruction, continuum Yang--Mills theory, or Clay conclusion
is inhabited here.  No `Classical.*`, choice, `native_decide`, `sorry`, custom
axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler
import YMGap.Continuum.SummableRationalSquareStepVariation
import YMGap.Continuum.SummableRationalStepVariation

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeRationalVariationCompiler

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel
open YMGap.Continuum.PhysicalSeparationSamplingOfSpacingToZero
open YMGap.Continuum.SummableRationalSquareStepVariation
open YMGap.Continuum.SummableRationalStepVariation

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Rational normalization-debt variation -/

/-- The minimal rational step/tail certificate for the actual reciprocal-
square normalization debt. -/
def MovingCubeNormalizationNormDebtRationalVariation
    (family : DynamicVacuumSectorCompletedFamily 0) : Type 1 :=
  SummableRationalStepVariation
    (fun scale => movingCubeNormalizationNormDebt family scale)

/-- Summable rational variation of the reciprocal normalization scale before
squaring.  This is a smaller local analytic quantity than the norm debt. -/
def MovingCubeNormalizationScaleRationalVariation
    (family : DynamicVacuumSectorCompletedFamily 0) : Type 1 :=
  SummableRationalStepVariation
    (fun scale => movingCubeNormalizationScale family scale)

/-- A varying reciprocal scale with one positive uniform ceiling has summable
variation after squaring, hence supplies the exact normalization-debt input.
The ceiling is an honest extra requirement; pointwise positivity alone does
not bound the reciprocal scales uniformly. -/
def movingCubeNormalizationNormDebtRationalVariationOfScale
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scaleVariation : MovingCubeNormalizationScaleRationalVariation family)
    (ceiling : Q') (ceiling_pos : (0 : Q') < ceiling)
    (scale_le_ceiling : forall scale,
      movingCubeNormalizationScale family scale <= ceiling) :
    MovingCubeNormalizationNormDebtRationalVariation family := by
  change SummableRationalStepVariation
    (fun scale =>
      movingCubeNormalizationScale family scale *
        movingCubeNormalizationScale family scale)
  exact SummableRationalSquareStepVariation.SummableRationalStepVariation.square
    scaleVariation ceiling ceiling_pos
    (fun scale => Q'.le_of_lt
      (movingCubeNormalizationScale_pos family scale))
    scale_le_ceiling

/-- A rational normalization-debt budget supplies the previously required
constructive-real variation with no additional analytic input. -/
def movingCubeNormalizationNormDebtVariationOfRational
    (family : DynamicVacuumSectorCompletedFamily 0)
    (data : MovingCubeNormalizationNormDebtRationalVariation family) :
    MovingCubeNormalizationNormDebtVariation family :=
  data.toSummableCRealStepVariation

/-! ## 2. Rational scheduled-rate variation -/

/-- Rational step/tail certificates for the exact scheduled squared-rate
power at every integer physical time. -/
def NormalizedMovingCubeSampledRatePowerRationalVariation
    (family : DynamicVacuumSectorCompletedFamily 0) : Type 1 :=
  forall time, SummableRationalStepVariation
    (fun scale => normalizedMovingCubeSampledRatePower family scale time)

/-- Rational scheduled-rate budgets supply the previously required
constructive-real variations pointwise in physical time. -/
def normalizedMovingCubeSampledRatePowerVariationOfRational
    (family : DynamicVacuumSectorCompletedFamily 0)
    (data : NormalizedMovingCubeSampledRatePowerRationalVariation family) :
    NormalizedMovingCubeSampledRatePowerVariation family :=
  fun time => (data time).toSummableCRealStepVariation

/-! ## 3. The zero-time rate branch is automatic -/

/-- Floor sampling at physical time zero uses exponent zero, so the exact
scheduled squared-rate power is pointwise one. -/
theorem normalizedMovingCubeSampledRatePower_zero_eqv_one
    (family : DynamicVacuumSectorCompletedFamily 0)
    (scale : Nat) :
    normalizedMovingCubeSampledRatePower family scale 0 ≈ (1 : Q') := by
  unfold normalizedMovingCubeSampledRatePower
  simp [centralPhysicalDynamicRCLatticeSteps,
    centralPhysicalDynamicRCSampling,
    physicalSeparationSamplingOfSpacingToZero, floorLatticeSteps]
  exact Q'.eqv_refl 1

/-- The exact zero-time scheduled-rate stream has the canonical zero
variation certificate. -/
def normalizedMovingCubeSampledRatePowerZeroRationalVariation
    (family : DynamicVacuumSectorCompletedFamily 0) :
    SummableRationalStepVariation
      (fun scale => normalizedMovingCubeSampledRatePower family scale 0) :=
  SummableRationalStepVariation.ofPointwiseEqvConstant
    (fun scale => normalizedMovingCubeSampledRatePower family scale 0) 1
    (normalizedMovingCubeSampledRatePower_zero_eqv_one family)

/-- It is enough to prove scheduled-rate rational variation at strictly
positive physical times; the time-zero branch is constructed above. -/
def normalizedMovingCubeSampledRatePowerRationalVariationOfPositive
    (family : DynamicVacuumSectorCompletedFamily 0)
    (positive : forall time, 0 < time ->
      SummableRationalStepVariation
        (fun scale => normalizedMovingCubeSampledRatePower
          family scale time)) :
    NormalizedMovingCubeSampledRatePowerRationalVariation family := by
  intro time
  cases time with
  | zero =>
      exact normalizedMovingCubeSampledRatePowerZeroRationalVariation family
  | succ time =>
      exact positive (time + 1) (Nat.zero_lt_succ time)

/-! ## 4. Rejoin rational debt/rate inputs with the genuine raw moment -/

/-- Raw `CReal` representative variation plus rational debt variation
construct the normalized same-observable continuum limit. -/
def normalizedMovingCubeLimitOfRationalDebtVariation
    (family : DynamicVacuumSectorCompletedFamily 0)
    (raw : MovingCubeRawScheduledRepresentativeVariation family)
    (normDebt : MovingCubeNormalizationNormDebtRationalVariation family) :
    NormalizedMovingCubeScheduledRCContinuumLimit family :=
  normalizedMovingCubeLimitOfVariations family raw
    (movingCubeNormalizationNormDebtVariationOfRational family normDebt)

/-- The rationalized raw/debt compiler retains strict continuum zero-time
positivity. -/
theorem normalizedMovingCubeLimitOfRationalDebtVariation_zero_isPositive
    (family : DynamicVacuumSectorCompletedFamily 0)
    (raw : MovingCubeRawScheduledRepresentativeVariation family)
    (normDebt : MovingCubeNormalizationNormDebtRationalVariation family) :
    RCStrictPositivity.RCIsPositive
      (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
        (normalizedMovingCubeLimitOfRationalDebtVariation
          family raw normDebt) 0) :=
  normalizedMovingCubeLimitOfVariations_zero_isPositive family raw
    (movingCubeNormalizationNormDebtVariationOfRational family normDebt)

/-- One genuine raw-moment variation plus two rational step/tail certificates
give the continuum squared-decay theorem for the exact normalized observable. -/
theorem normalizedMovingCubeLimitOfRationalVariations_sq_decay
    (family : DynamicVacuumSectorCompletedFamily 0)
    (raw : MovingCubeRawScheduledRepresentativeVariation family)
    (normDebt : MovingCubeNormalizationNormDebtRationalVariation family)
    (ratePower : NormalizedMovingCubeSampledRatePowerRationalVariation family)
    (time : Nat) :
    CReal.RCle
      (CReal.RCmul
        (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
          (normalizedMovingCubeLimitOfRationalDebtVariation
            family raw normDebt) time)
        (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
          (normalizedMovingCubeLimitOfRationalDebtVariation
            family raw normDebt) time))
      (CReal.RCmul
        (CReal.RCmul
          (Quotient.mk CReal.crealSetoid
            ((normalizedMovingCubeSampledRatePowerLimitOfVariation family
              (normalizedMovingCubeSampledRatePowerVariationOfRational
                family ratePower)).limitRepresentative time))
          (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
            (normalizedMovingCubeLimitOfRationalDebtVariation
              family raw normDebt) 0))
        (NormalizedMovingCubeScheduledRCContinuumLimit.continuumConnectedAutocorrelation
          (normalizedMovingCubeLimitOfRationalDebtVariation
            family raw normDebt) 0)) :=
  normalizedMovingCubeLimitOfVariations_sq_decay family raw
    (movingCubeNormalizationNormDebtVariationOfRational family normDebt)
    (normalizedMovingCubeSampledRatePowerVariationOfRational family ratePower)
    time

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeRationalVariationCompiler

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeRationalVariationCompiler.movingCubeNormalizationNormDebtVariationOfRational
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeRationalVariationCompiler.movingCubeNormalizationNormDebtRationalVariationOfScale
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeRationalVariationCompiler.normalizedMovingCubeSampledRatePowerVariationOfRational
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeRationalVariationCompiler.normalizedMovingCubeSampledRatePower_zero_eqv_one
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeRationalVariationCompiler.normalizedMovingCubeSampledRatePowerZeroRationalVariation
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeRationalVariationCompiler.normalizedMovingCubeSampledRatePowerRationalVariationOfPositive
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeRationalVariationCompiler.normalizedMovingCubeLimitOfRationalDebtVariation_zero_isPositive
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeRationalVariationCompiler.normalizedMovingCubeLimitOfRationalVariations_sq_decay
