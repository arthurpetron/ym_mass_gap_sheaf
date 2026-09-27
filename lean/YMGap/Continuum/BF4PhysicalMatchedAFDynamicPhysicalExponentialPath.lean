/-
# Matched AF trajectory through the adaptive physical-exponential consumer

The exact matched-AF dynamic compiler already identifies the nome with the
literal matched block weight and the spacing with the supplied physical
spacing envelope.  The adaptive physical-exponential module is generic in
that completed family.  This module is the typed adapter: it keeps the
matched trajectory and the same local producer in scope while exposing the
generic physical-exponential limit, same-object squared-decay estimate, and
certificate on that exact family.

The raw representative variation, normalization-debt variation, physical
strength band, physical-gap variation, and positive-time scheduled-rate
variation remain explicit fields.  Nothing here constructs the local
producer, the scaling estimates, OS/GNS data, a continuum Yang--Mills theory,
or the Clay conclusion.  No `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler
import YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptivePhysicalExponentialPath
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalExponentialCertificate

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubePath
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubePath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptivePhysicalExponentialPath
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptivePhysicalExponentialPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalExponentialCertificate
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerEulerCorridor
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerEulerCorridor.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerPhysicalExponentialCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler
open YMGap.Continuum.SummableRationalStepVariationPrefixTailClosure

namespace MatchedPhysicalDynamicScalarTrajectory

/-! ## 1. Names for the exact matched adaptive family -/

/-- The adaptive family generated from the literal matched trajectory and its
local capacity/transition producer. -/
abbrev adaptiveFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (producer : trajectory.LocalProducer) :
    DynamicSpinCubeOffRayAdaptiveTransitionProductFamily :=
  trajectory.toDynamicFamily producer

/-- Raw same-object representative variation for the exact matched family. -/
abbrev MovingCubeRawVariation
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (producer : trajectory.LocalProducer) : Type 1 :=
  BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.MovingCubeRawVariation
    (adaptiveFamily trajectory producer)

/-- Rational normalization-debt variation for the exact matched family. -/
abbrev MovingCubeNormalizationDebtRationalVariation
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (producer : trajectory.LocalProducer) : Type 1 :=
  BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.MovingCubeNormalizationDebtRationalVariation
    (adaptiveFamily trajectory producer)

/-- The physical-gap variation input for the exact matched completed family. -/
abbrev PhysicalGapRationalVariation
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (producer : trajectory.LocalProducer) : Type 1 :=
  BF4PhysicalDynamicSpinCubeOffRayAdaptivePhysicalExponentialPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.PhysicalGapRationalVariation
    (adaptiveFamily trajectory producer)

/-- Positive-time rate-power variation for the exact matched family. -/
abbrev PositiveMovingCubeRatePowerRationalVariation
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (producer : trajectory.LocalProducer) : Type 1 :=
  BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.PositiveMovingCubeRatePowerRationalVariation
    (adaptiveFamily trajectory producer)

/-- The physical strength band remains attached to the same completed
matched transfer selected by the local producer. -/
abbrev StrengthBand
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (producer : trajectory.LocalProducer) : Type 1 :=
  (adaptiveFamily trajectory producer).StrengthBand

/-! ## 2. Exact physical-exponential consequences -/

/-- The scheduled physical-exponential rate-power limit for the literal
matched completed family. -/
def physicalExponentialLimit
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (producer : trajectory.LocalProducer)
    (positiveRatePower : PositiveMovingCubeRatePowerRationalVariation trajectory producer) :
    NormalizedMovingCubeSampledRatePowerLimit
      (trajectory.toCompletedFamily producer) :=
  BF4PhysicalDynamicSpinCubeOffRayAdaptivePhysicalExponentialPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.physicalExponentialLimit
    (adaptiveFamily trajectory producer)
    positiveRatePower

@[simp] theorem physicalExponentialLimit_toCompletedFamily
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (producer : trajectory.LocalProducer)
    (positiveRatePower : PositiveMovingCubeRatePowerRationalVariation trajectory producer) :
    physicalExponentialLimit trajectory producer positiveRatePower =
      BF4PhysicalDynamicSpinCubeOffRayAdaptivePhysicalExponentialPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.physicalExponentialLimit
        (adaptiveFamily trajectory producer) positiveRatePower :=
  rfl

/- The generic theorem is re-exposed with the matched trajectory in every
dependent position.  This is the main same-object consumer of the adapter. -/
theorem physicalExponentialLimit_identification
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (producer : trajectory.LocalProducer)
    (band : StrengthBand trajectory producer)
    (gapVariation : PhysicalGapRationalVariation trajectory producer)
    (positiveRatePower : PositiveMovingCubeRatePowerRationalVariation trajectory producer)
    (time : Nat) :
    CReal.ConvergesTo
        (fun scale => scheduledSquaredRateUpperExponential
          (adaptiveFamily trajectory producer).toCompletedFamily scale time)
        ((physicalExponentialLimit trajectory producer positiveRatePower).limitRepresentative
          time) /\
      CReal.ConvergesTo
        (fun scale => scheduledSquaredRateLowerExponential
          (adaptiveFamily trajectory producer).toCompletedFamily
          (BF4PhysicalDynamicVacuumSectorScheduledRatePowerEulerCorridor.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.completedRate_pos
            (adaptiveFamily trajectory producer))
          scale time)
        ((physicalExponentialLimit trajectory producer positiveRatePower).limitRepresentative
          time) := by
  exact BF4PhysicalDynamicSpinCubeOffRayAdaptivePhysicalExponentialPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.physicalExponentialLimit_identification
    (adaptiveFamily trajectory producer) band gapVariation positiveRatePower time

/-- Same-object squared continuum decay for the exact matched-AF family.  The
rate-power limit and the connected autocorrelation share the same completed
carrier and observable lineage. -/
theorem normalizedMovingCubePhysicalExponential_sq_decay
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (producer : trajectory.LocalProducer)
    (raw : MovingCubeRawVariation trajectory producer)
    (normalizationDebt :
      MovingCubeNormalizationDebtRationalVariation trajectory producer)
    (band : StrengthBand trajectory producer)
    (gapVariation : PhysicalGapRationalVariation trajectory producer)
    (positiveRatePower :
      PositiveMovingCubeRatePowerRationalVariation trajectory producer)
    (time : Nat) :
    CReal.RCle
        (CReal.RCmul
          (normalizedMovingCubeContinuumConnectedAutocorrelation
            (normalizedMovingCubeContinuumLimitOfRationalVariations
              (adaptiveFamily trajectory producer) raw normalizationDebt) time)
          (normalizedMovingCubeContinuumConnectedAutocorrelation
            (normalizedMovingCubeContinuumLimitOfRationalVariations
              (adaptiveFamily trajectory producer) raw normalizationDebt) time))
        (CReal.RCmul
          (CReal.RCmul
            (Quotient.mk CReal.crealSetoid
              ((physicalExponentialLimit trajectory producer positiveRatePower).limitRepresentative
                time))
            (normalizedMovingCubeContinuumConnectedAutocorrelation
              (normalizedMovingCubeContinuumLimitOfRationalVariations
            (adaptiveFamily trajectory producer) raw normalizationDebt) 0))
          (normalizedMovingCubeContinuumConnectedAutocorrelation
            (normalizedMovingCubeContinuumLimitOfRationalVariations
            (adaptiveFamily trajectory producer) raw normalizationDebt) 0)) := by
  exact
    (BF4PhysicalDynamicSpinCubeOffRayAdaptivePhysicalExponentialPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.normalizedMovingCubePhysicalExponential_sq_decay
      (adaptiveFamily trajectory producer) raw normalizationDebt band gapVariation
        positiveRatePower time).1

/-! ## 3. Contract the inputs into the existing physical-exponential record -/

/-- All supplied variations and the physical band compile to the existing
same-family physical-exponential certificate, now indexed by the literal
matched trajectory. -/
def toPhysicalExponentialCertificate
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (producer : trajectory.LocalProducer)
    (raw : MovingCubeRawVariation trajectory producer)
    (normalizationDebt :
      MovingCubeNormalizationDebtRationalVariation trajectory producer)
    (band : StrengthBand trajectory producer)
    (gapVariation : PhysicalGapRationalVariation trajectory producer)
    (positiveRatePower :
      PositiveMovingCubeRatePowerRationalVariation trajectory producer) :
    NormalizedMovingCubePhysicalExponentialCertificate
      (trajectory.toCompletedFamily producer) :=
  NormalizedMovingCubePhysicalExponentialCertificate.ofRationalVariations
    (adaptiveFamily trajectory producer).toCompletedFamily
    raw normalizationDebt
    ((adaptiveFamily trajectory producer).physicalRateBand band)
    (BF4PhysicalDynamicVacuumSectorScheduledRatePowerEulerCorridor.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.completedRate_pos
      (adaptiveFamily trajectory producer))
    gapVariation
    (BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.movingCubeRatePowerRationalVariationOfPositive
      (adaptiveFamily trajectory producer) positiveRatePower)

/-! ## 4. Contract the local producer to the correlated same-edge debt seam -/

/-- The correlated capacity-debt compiler supplies the exact local producer
for the matched trajectory.  This is the smallest named route from the
same-edge envelope/tail/slack obligations into the physical-exponential
consumer; no scaling or continuum input is inferred here. -/
def localProducer_ofCorrelatedCapacityDebt
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (envelope : forall physicalScale,
      MatchedEventualCanonicalCorrelatedCapacityDebtEnvelope
        trajectory transitionStart physicalScale)
    (tailAllowance : Nat -> Q')
    (tailAllowance_pos : forall physicalScale,
      (0 : Q') < tailAllowance physicalScale)
    (initial_closure : forall physicalScale,
      matchedEventualCanonicalRoutedCapacityDebtMaximum
            trajectory transitionStart physicalScale 0 +
          prefixTailTotalBudget
            (matchedEventualCanonicalRoutedCapacityDebtMaximumVariation
              (envelope physicalScale))
            (tailAllowance physicalScale) <=
        (1 : Q')) :
    trajectory.LocalProducer :=
  matchedEventualCanonicalCorrelatedCapacityDebtLocalProducer
    trajectory transitionStart envelope tailAllowance tailAllowance_pos
      initial_closure

/-- Direct physical-exponential contraction from the correlated same-edge
debt certificate.  The raw representative, normalization debt, strength
band, physical-gap variation, and positive-time rate variation remain
explicit arguments on the identical completed matched carrier. -/
def toPhysicalExponentialCertificate_ofCorrelatedCapacityDebt
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (envelope : forall physicalScale,
      MatchedEventualCanonicalCorrelatedCapacityDebtEnvelope
        trajectory transitionStart physicalScale)
    (tailAllowance : Nat -> Q')
    (tailAllowance_pos : forall physicalScale,
      (0 : Q') < tailAllowance physicalScale)
    (initial_closure : forall physicalScale,
      matchedEventualCanonicalRoutedCapacityDebtMaximum
            trajectory transitionStart physicalScale 0 +
          prefixTailTotalBudget
            (matchedEventualCanonicalRoutedCapacityDebtMaximumVariation
              (envelope physicalScale))
            (tailAllowance physicalScale) <=
        (1 : Q'))
    (raw : MovingCubeRawVariation trajectory
      (localProducer_ofCorrelatedCapacityDebt trajectory transitionStart
        envelope tailAllowance tailAllowance_pos initial_closure))
    (normalizationDebt : MovingCubeNormalizationDebtRationalVariation trajectory
      (localProducer_ofCorrelatedCapacityDebt trajectory transitionStart
        envelope tailAllowance tailAllowance_pos initial_closure))
    (band : StrengthBand trajectory
      (localProducer_ofCorrelatedCapacityDebt trajectory transitionStart
        envelope tailAllowance tailAllowance_pos initial_closure))
    (gapVariation : PhysicalGapRationalVariation trajectory
      (localProducer_ofCorrelatedCapacityDebt trajectory transitionStart
        envelope tailAllowance tailAllowance_pos initial_closure))
    (positiveRatePower : PositiveMovingCubeRatePowerRationalVariation trajectory
      (localProducer_ofCorrelatedCapacityDebt trajectory transitionStart
        envelope tailAllowance tailAllowance_pos initial_closure)) :
    NormalizedMovingCubePhysicalExponentialCertificate
      (trajectory.toCompletedFamily
        (localProducer_ofCorrelatedCapacityDebt trajectory transitionStart
          envelope tailAllowance tailAllowance_pos initial_closure)) :=
  toPhysicalExponentialCertificate trajectory
    (localProducer_ofCorrelatedCapacityDebt trajectory transitionStart envelope
      tailAllowance tailAllowance_pos initial_closure)
    raw normalizationDebt band gapVariation positiveRatePower

end MatchedPhysicalDynamicScalarTrajectory

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.physicalExponentialLimit_identification
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.normalizedMovingCubePhysicalExponential_sq_decay
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.toPhysicalExponentialCertificate
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.localProducer_ofCorrelatedCapacityDebt
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.toPhysicalExponentialCertificate_ofCorrelatedCapacityDebt
