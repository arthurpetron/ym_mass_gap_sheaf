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
import YMGap.Continuum.PhysicalSeparatorFullLogComparison
import YMGap.Continuum.PhysicalSeparatorFullLogHalfWindow
import YMGap.Continuum.PhysicalSeparatorContinuumRealization
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicRescaledStrengthCompiler

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
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorFullLogComparison
open YMGap.Continuum.PhysicalSeparatorFullLogHalfWindow
open YMGap.Continuum.PhysicalSeparatorFullLogRate
open YMGap.Continuum.PhysicalSeparatorContinuumRealization
open YMGap.Continuum.PhysicalSeparatorLinearTail
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler.DynamicVacuumSectorObservablePin
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicRescaledStrengthCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicStrengthNormalization
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.BF4AFPhysicalSpacingToZero
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRescaledStrengthTracking
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayResidualStrengthVariationCompiler
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorUniformMassFloor
open YMGap.Continuum.SummableRationalStepVariation
open YMGap.Continuum.QuadraticRateErrorTailControl
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.MeasureLinkedOSReconstruction
open YMGap.Continuum.ExactRateReconstructionHandoff
open YMGap.Continuum.ProjectiveOSCorrelationHandoff

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

/-! ## 4. Keep the nonzero observable on the identical completed carrier -/

/-- A physical-exponential certificate and the same-object observable pin are
kept in one dependent record.  The pin is indexed by the very completed
matched family used by the exponential certificate, so this record cannot
silently mix observables or carriers. -/
structure PhysicalExponentialObservableWitness
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (producer : trajectory.LocalProducer) : Type 2 where
  exponential : NormalizedMovingCubePhysicalExponentialCertificate
    (trajectory.toCompletedFamily producer)
  observable : trajectory.SameObjectObservablePin producer

namespace PhysicalExponentialObservableWitness

/-- Attach an already checked exponential certificate to an exact same-object
observable pin without changing any family index. -/
def ofCertificate
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (producer : trajectory.LocalProducer)
    (exponential : NormalizedMovingCubePhysicalExponentialCertificate
      (trajectory.toCompletedFamily producer))
    (observable : trajectory.SameObjectObservablePin producer) :
    PhysicalExponentialObservableWitness trajectory producer :=
  { exponential := exponential, observable := observable }

/-- Produce the bundled witness from the explicit scaling inputs and the
same-family observable pin. -/
def ofRationalVariations
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
    (observable : trajectory.SameObjectObservablePin producer) :
    PhysicalExponentialObservableWitness trajectory producer :=
  ofCertificate trajectory producer
    (toPhysicalExponentialCertificate trajectory producer raw normalizationDebt
      band gapVariation positiveRatePower)
    observable

/-- The bundled witness retains the physical separator selected by its exact
observable pin. -/
def physicalSeparator
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (witness : PhysicalExponentialObservableWitness trajectory producer) :
    PhysicalSeparator :=
  trajectory.physicalSeparator witness.observable

theorem physicalSeparator_gapObservable_zero_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (witness : PhysicalExponentialObservableWitness trajectory producer)
    (scale : Nat) :
    (0 : Q') <
      (physicalSeparator witness).corrIface.connectedCorr
        scale witness.observable.gapObservable 0 :=
  trajectory.physicalSeparator_gapObservable_zero_pos witness.observable scale

end PhysicalExponentialObservableWitness

/-! ## 5. Expose the exact-log physical-gap obligations -/

/-- The observable witness selects the exact separator and completed-family
spacing used by the full-range logarithmic compiler.  A physical-gap floor and
finite exact-rate ceiling remain explicit, so this adapter cannot turn the
finite exponential certificate into a continuum mass gap by coercion. -/
def toFullRangeExactPhysicalSeparatorCertificate
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (witness :
      PhysicalExponentialObservableWitness trajectory producer)
    (gapFloor :
      PhysicalGapFloor
        (PhysicalExponentialObservableWitness.physicalSeparator witness)
        (trajectory.toCompletedFamily producer).transferSpacing.spacing
        (trajectory.toCompletedFamily producer).transferSpacing.spacing_pos)
    (ceiling :
      FullRangeLogRateCeiling
        (fullRangeRateFamilyOfPhysicalData
          (PhysicalExponentialObservableWitness.physicalSeparator witness)
          (trajectory.toCompletedFamily producer).transferSpacing.spacing
          (trajectory.toCompletedFamily producer).transferSpacing.spacing_pos)) :
    FullRangeExactPhysicalSeparatorCertificate :=
  fullRangeExactCertificateOfPhysicalGapFloor
    (PhysicalExponentialObservableWitness.physicalSeparator witness)
    (trajectory.toCompletedFamily producer).transferSpacing.spacing
    (trajectory.toCompletedFamily producer).transferSpacing.spacing_pos
    gapFloor ceiling

/-- The exact-log certificate contracts further to cutoff removal from the
explicit Cauchy modulus of the exact physical-rate sequence and the supplied
spacing-to-zero modulus.  The existing constructive limit compiler derives
both surviving band inequalities; no continuum measure or OS datum is chosen.
-/
def toExactRateCutoffRemoval
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (witness :
      PhysicalExponentialObservableWitness trajectory producer)
    (gapFloor :
      PhysicalGapFloor
        (PhysicalExponentialObservableWitness.physicalSeparator witness)
        (trajectory.toCompletedFamily producer).transferSpacing.spacing
        (trajectory.toCompletedFamily producer).transferSpacing.spacing_pos)
    (ceiling :
      FullRangeLogRateCeiling
        (fullRangeRateFamilyOfPhysicalData
          (PhysicalExponentialObservableWitness.physicalSeparator witness)
          (trajectory.toCompletedFamily producer).transferSpacing.spacing
          (trajectory.toCompletedFamily producer).transferSpacing.spacing_pos))
    (spacingToZero :
      SpacingToZero
        (fullRangeRateFamilyOfPhysicalData
          (PhysicalExponentialObservableWitness.physicalSeparator witness)
          (trajectory.toCompletedFamily producer).transferSpacing.spacing
          (trajectory.toCompletedFamily producer).transferSpacing.spacing_pos).physicalSpacing)
    (rateCauchy :
      CReal.ModCauchyEv
        (fullRangeRateFamilyOfPhysicalData
          (PhysicalExponentialObservableWitness.physicalSeparator witness)
          (trajectory.toCompletedFamily producer).transferSpacing.spacing
          (trajectory.toCompletedFamily producer).transferSpacing.spacing_pos).rate) :
    ExactRateCutoffRemoval
      (toFullRangeExactPhysicalSeparatorCertificate witness gapFloor ceiling) :=
  ExactRateLimitData.withSpacing
    (ExactRateLimitData.ofRateCauchy rateCauchy) spacingToZero

/-- Specialized cutoff removal using the spacing-to-zero modulus already
stored on the matched scalar trajectory.  Only the exact-rate Cauchy modulus
remains a new analytic input at this boundary. -/
def toExactRateCutoffRemoval_ofTrajectorySpacing
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (witness :
      PhysicalExponentialObservableWitness trajectory producer)
    (gapFloor :
      PhysicalGapFloor
        (PhysicalExponentialObservableWitness.physicalSeparator witness)
        (trajectory.toCompletedFamily producer).transferSpacing.spacing
        (trajectory.toCompletedFamily producer).transferSpacing.spacing_pos)
    (ceiling :
      FullRangeLogRateCeiling
        (fullRangeRateFamilyOfPhysicalData
          (PhysicalExponentialObservableWitness.physicalSeparator witness)
          (trajectory.toCompletedFamily producer).transferSpacing.spacing
          (trajectory.toCompletedFamily producer).transferSpacing.spacing_pos))
    (rateCauchy :
      CReal.ModCauchyEv
        (fullRangeRateFamilyOfPhysicalData
          (PhysicalExponentialObservableWitness.physicalSeparator witness)
          (trajectory.toCompletedFamily producer).transferSpacing.spacing
          (trajectory.toCompletedFamily producer).transferSpacing.spacing_pos).rate) :
    ExactRateCutoffRemoval
      (toFullRangeExactPhysicalSeparatorCertificate witness gapFloor ceiling) :=
  toExactRateCutoffRemoval witness gapFloor ceiling
    trajectory.transferSpacingToZero rateCauchy

/-- Strength scaling itself supplies the physical-gap floor required by the
exact-log compiler.  This constructor keeps only the independent full-log
ceiling explicit. -/
def toFullRangeExactPhysicalSeparatorCertificate_ofStrengthBand
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (witness :
      PhysicalExponentialObservableWitness trajectory producer)
    (band : StrengthBand trajectory producer)
    (ceiling :
      FullRangeLogRateCeiling
        (YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.fullRangeRateFamily
          witness.observable)) :
    FullRangeExactPhysicalSeparatorCertificate :=
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.exactCertificate witness.observable
    ((adaptiveFamily trajectory producer).physicalRateBand band) ceiling

/-! ## 5a. Reduce the full-log ceiling to a finite prefix

The matched physical-rate band already contains the cross-multiplied tail
estimate needed by `PhysicalSeparatorLinearTail`.  Consequently its spacing
modulus computes an eventual half-window and an exact-log tail ceiling.  Only
the finitely many earlier exact rates remain as an explicit certificate. -/

/-- The finite-prefix input required after the matched rate band has supplied
the asymptotic exact-log ceiling.  Its index is computed from the same
observable and the same completed-family physical-rate band. -/
abbrev FullRangeLogRatePrefixCeiling
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (witness : PhysicalExponentialObservableWitness trajectory producer)
    (band : StrengthBand trajectory producer) : Type :=
  PrefixFullRangeLogRateCeiling
    (YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.fullRangeRateFamily witness.observable)
    (YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler.DynamicVacuumSectorObservablePin.exactLogRateStart
      witness.observable
      ((adaptiveFamily trajectory producer).physicalRateBand band))

/-- The matched physical-rate band and a finite exact-rate prefix construct a
single global full-range logarithmic ceiling.  The tail constant is the
explicit `9/4` direct-log constant times the same physical-rate ceiling; no
unrelated separator or spacing schedule is introduced. -/
def toFullRangeLogRateCeiling_ofStrengthBandAndPrefix
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (witness : PhysicalExponentialObservableWitness trajectory producer)
    (band : StrengthBand trajectory producer)
    (pre : FullRangeLogRatePrefixCeiling witness band) :
    FullRangeLogRateCeiling
      (YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.fullRangeRateFamily witness.observable) := by
  let matchedBand := (adaptiveFamily trajectory producer).physicalRateBand band
  let linear :=
    YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler.DynamicVacuumSectorObservablePin.exactLogLinearMarginTail
      witness.observable matchedBand
  let spacingToZero :=
    (trajectory.toCompletedFamily producer).transferSpacingToZero
  exact globalExactCeilingOfPrefixEventualHalfWindow
    witness.observable.toPhysicalSeparator
    (trajectory.toCompletedFamily producer).transferSpacing
    (linear.eventualStart spacingToZero)
    pre
    (linear.toEventualHalfWindow
      spacingToZero)
    (linear.toTailMarginRateCeiling
      spacingToZero)

@[simp] theorem toFullRangeLogRateCeiling_ofStrengthBandAndPrefix_ceiling
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (witness : PhysicalExponentialObservableWitness trajectory producer)
    (band : StrengthBand trajectory producer)
    (pre : FullRangeLogRatePrefixCeiling witness band) :
    (toFullRangeLogRateCeiling_ofStrengthBandAndPrefix witness band pre).ceiling =
      Q'.max' pre.ceiling
        (YMGap.Continuum.EffMassConvergence.c94 *
          ((adaptiveFamily trajectory producer).physicalRateBand band).ceiling) := by
  rfl

/-- The finite-prefix reduction packages directly into the same completed
physical separator certificate used by the exact-rate and continuum
consumers. -/
def toFullRangeExactPhysicalSeparatorCertificate_ofStrengthBandAndPrefix
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (witness : PhysicalExponentialObservableWitness trajectory producer)
    (band : StrengthBand trajectory producer)
    (pre : FullRangeLogRatePrefixCeiling witness band) :
    FullRangeExactPhysicalSeparatorCertificate :=
  toFullRangeExactPhysicalSeparatorCertificate_ofStrengthBand witness band
    (toFullRangeLogRateCeiling_ofStrengthBandAndPrefix witness band pre)

/-! ## 5b. Compute the finite prefix from the matched physical-rate band

`BF4PhysicalMatchedAFDynamicRescaledStrengthCompiler` already proves that the
same physical-rate band supplies the eventual half-window and computes the
finite exact-rate prefix from the separator's constructive logarithm bounds.
The adapter below exposes that stronger route at the matched observable
witness, eliminating the finite-prefix field without changing the carrier. -/

/-- The matched strength band computes a global full-range logarithmic ceiling
on the same observable and completed physical family. -/
def toFullRangeLogRateCeiling_ofStrengthBandComputed
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (witness : PhysicalExponentialObservableWitness trajectory producer)
    (band : StrengthBand trajectory producer) :
    FullRangeLogRateCeiling
      (YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.fullRangeRateFamily witness.observable) :=
  fullRangeLogRateCeilingOfPhysicalRateBand witness.observable
    ((adaptiveFamily trajectory producer).physicalRateBand band)

/-- Package the computed full-log ceiling directly into the exact physical
separator certificate used by the cutoff and continuum consumers. -/
def toFullRangeExactPhysicalSeparatorCertificate_ofStrengthBandComputed
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (witness : PhysicalExponentialObservableWitness trajectory producer)
    (band : StrengthBand trajectory producer) :
    FullRangeExactPhysicalSeparatorCertificate :=
  toFullRangeExactPhysicalSeparatorCertificate_ofStrengthBand witness band
    (toFullRangeLogRateCeiling_ofStrengthBandComputed witness band)

/-- Same-family physical-gap variation and an inverse-square spacing tail
construct the exact-rate cutoff removal, while the full-log ceiling remains a
separate analytic input. -/
def toExactRateCutoffRemoval_ofGapVariation
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (witness :
      PhysicalExponentialObservableWitness trajectory producer)
    (band : StrengthBand trajectory producer)
    (ceiling :
      FullRangeLogRateCeiling
        (YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.fullRangeRateFamily
          witness.observable))
    (gapVariation : PhysicalGapRationalVariation trajectory producer)
    (spacingTail :
      InverseSquareSpacingTail
        (trajectory.toCompletedFamily producer).transferSpacing 0) :
    ExactRateCutoffRemoval
      (toFullRangeExactPhysicalSeparatorCertificate_ofStrengthBand
        witness band ceiling) :=
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler.DynamicVacuumSectorObservablePin.exactRateCutoffRemovalOfVariations
    witness.observable
    ((adaptiveFamily trajectory producer).physicalRateBand band)
    ceiling gapVariation spacingTail

/-- The finite-prefix reduction can be consumed directly by the exact-rate
cutoff-removal compiler.  This keeps the only non-asymptotic input visible as
the prefix certificate rather than reintroducing a global opaque ceiling. -/
def toExactRateCutoffRemoval_ofGapVariationAndPrefix
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (witness :
      PhysicalExponentialObservableWitness trajectory producer)
    (band : StrengthBand trajectory producer)
    (pre : FullRangeLogRatePrefixCeiling witness band)
    (gapVariation : PhysicalGapRationalVariation trajectory producer)
    (spacingTail :
      InverseSquareSpacingTail
        (trajectory.toCompletedFamily producer).transferSpacing 0) :
    ExactRateCutoffRemoval
      (toFullRangeExactPhysicalSeparatorCertificate_ofStrengthBandAndPrefix
        witness band pre) :=
  toExactRateCutoffRemoval_ofGapVariation witness band
    (toFullRangeLogRateCeiling_ofStrengthBandAndPrefix witness band pre)
    gapVariation spacingTail

/-- The computed full-log ceiling can be consumed directly by exact-rate
cutoff removal, leaving only same-family gap variation and spacing-tail data. -/
def toExactRateCutoffRemoval_ofGapVariationAndComputedCeiling
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (witness : PhysicalExponentialObservableWitness trajectory producer)
    (band : StrengthBand trajectory producer)
    (gapVariation : PhysicalGapRationalVariation trajectory producer)
    (spacingTail :
      InverseSquareSpacingTail
        (trajectory.toCompletedFamily producer).transferSpacing 0) :
    ExactRateCutoffRemoval
      (toFullRangeExactPhysicalSeparatorCertificate_ofStrengthBandComputed
        witness band) :=
  toExactRateCutoffRemoval_ofGapVariation witness band
    (toFullRangeLogRateCeiling_ofStrengthBandComputed witness band)
    gapVariation spacingTail

/-! ## 5c. Replace primitive gap variation by rescaled-strength variation

The rescaled-strength compiler controls the same exact-log rate using the
physical gap plus the vanishing normalization correction, without asking for
variation of reciprocal spacing.  This adapter exposes that smaller analytic
input on the same observable witness and uses the already computed full-log
ceiling. -/

/-- Same-carrier cutoff removal from a summable rescaled-strength variation,
with the full-log ceiling computed from the scaling band. -/
def toExactRateCutoffRemoval_ofRescaledStrengthAndComputedCeiling
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (witness : PhysicalExponentialObservableWitness trajectory producer)
    (scaling : MatchedPhysicalDynamicStrengthScaling trajectory producer)
    (variation : SummableRationalStepVariation
      (rescaledStrength
        (trajectory.toNormalizedStrengthLaw producer)))
    (C : AFTrajectoryCertificate)
    (H : ShiftedAFTrajectoryIdentification C trajectory.coupling) :
    ExactRateCutoffRemoval
      (YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.exactCertificate
        witness.observable
        (scaling.toPhysicalRateBand)
        (fullRangeLogRateCeilingOfPhysicalRateBand
          witness.observable scaling.toPhysicalRateBand)) :=
  matchedExactRateCutoffRemovalOfRescaledStrengthOfPhysicalRateBand
    trajectory producer scaling witness.observable variation C H

/-- Same-carrier continuum handoff from rescaled-strength variation, with the
full-log ceiling computed from the matched scaling band. -/
def toContinuumHandoff_ofRescaledStrengthAndComputedCeiling
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (witness : PhysicalExponentialObservableWitness trajectory producer)
    (scaling : MatchedPhysicalDynamicStrengthScaling trajectory producer)
    (variation : SummableRationalStepVariation
      (rescaledStrength
        (trajectory.toNormalizedStrengthLaw producer)))
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {existence : ContinuumYMExistence mu}
    {osGNS : MeasureLinkedOSGNSData existence}
    (projectiveOS : ProjectiveOSCorrelationHandoff
      witness.observable.toPhysicalSeparator existence osGNS
        witness.observable.physicalSampling)
    (spectralChannel :
      ProjectiveOSCorrelationHandoff.ReconstructionSpectralChannelHandoff
        projectiveOS osGNS.reconstruction)
    (exactRate : ExactRateReconstructionHandoff
      (YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.exactCertificate
        witness.observable
        (scaling.toPhysicalRateBand)
        (fullRangeLogRateCeilingOfPhysicalRateBand
          witness.observable scaling.toPhysicalRateBand))
      osGNS.reconstruction)
    (C : AFTrajectoryCertificate)
    (H : ShiftedAFTrajectoryIdentification C trajectory.coupling) :
    YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.DynamicVacuumSectorContinuumHandoff
      witness.observable
      (scaling.toPhysicalRateBand)
      (fullRangeLogRateCeilingOfPhysicalRateBand
        witness.observable scaling.toPhysicalRateBand)
      existence osGNS :=
  matchedContinuumHandoffOfRescaledStrength
    trajectory producer scaling witness.observable variation
    (fullRangeLogRateCeilingOfPhysicalRateBand
      witness.observable scaling.toPhysicalRateBand)
    projectiveOS spectralChannel exactRate C H

/-! ## 5d. Factor the rescaled variation into primitive streams -/

/-- Same-carrier cutoff removal after factoring rescaled-strength variation
into physical-gap and normalized-strength variations. -/
def toExactRateCutoffRemoval_ofPhysicalGapAndStrengthAndComputedCeiling
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (witness : PhysicalExponentialObservableWitness trajectory producer)
    (scaling : MatchedPhysicalDynamicStrengthScaling trajectory producer)
    (gapVariation : SummableRationalStepVariation
      (trajectory.toCompletedFamily producer).physicalGap)
    (strengthVariation : SummableRationalStepVariation
      (trajectory.toNormalizedStrengthLaw producer).strength)
    (C : AFTrajectoryCertificate)
    (H : ShiftedAFTrajectoryIdentification C trajectory.coupling) :
    ExactRateCutoffRemoval
      (YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.exactCertificate
        witness.observable
        (scaling.toPhysicalRateBand)
        (fullRangeLogRateCeilingOfPhysicalRateBand
          witness.observable scaling.toPhysicalRateBand)) :=
  toExactRateCutoffRemoval_ofRescaledStrengthAndComputedCeiling
    witness scaling
    (rescaledStrengthVariationOfPhysicalGapAndStrength
      (trajectory.toNormalizedStrengthLaw producer)
      gapVariation strengthVariation)
    C H

/-- Same-carrier cutoff removal after reducing normalized-strength variation to
the literal ray-capacity and finite-sector mass-floor streams. -/
def toExactRateCutoffRemoval_ofRayCapacityAndMassFloorAndPhysicalGapAndComputedCeiling
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (witness : PhysicalExponentialObservableWitness trajectory producer)
    (scaling : MatchedPhysicalDynamicStrengthScaling trajectory producer)
    (rayDeltaVariation : SummableRationalStepVariation
      (fun scale =>
        (((trajectory.toDynamicFamily producer).toResidualCoercivityFamily.rayCapacity
          scale).delta)))
    (massFloorVariation : SummableRationalStepVariation
      (fun scale =>
        centralPhysicalFiniteVacuumSectorUniformMassFloor
          ((trajectory.toDynamicFamily producer).toResidualCoercivityFamily.nome
            scale)
          (Q'.le_of_lt
            ((trajectory.toDynamicFamily producer).toResidualCoercivityFamily.nome_pos
              scale)) 0))
    (gapVariation : SummableRationalStepVariation
      (trajectory.toCompletedFamily producer).physicalGap)
    (C : AFTrajectoryCertificate)
    (H : ShiftedAFTrajectoryIdentification C trajectory.coupling) :
    ExactRateCutoffRemoval
      (YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.exactCertificate
        witness.observable
        (scaling.toPhysicalRateBand)
        (fullRangeLogRateCeilingOfPhysicalRateBand
          witness.observable scaling.toPhysicalRateBand)) :=
  matchedExactRateCutoffRemovalOfRayCapacityAndMassFloorAndPhysicalGapOfPhysicalRateBand
    trajectory producer scaling witness.observable rayDeltaVariation
    massFloorVariation gapVariation C H

/-- Same-carrier continuum handoff after factoring rescaled-strength variation
into physical-gap and normalized-strength variations. -/
def toContinuumHandoff_ofPhysicalGapAndStrengthAndComputedCeiling
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (witness : PhysicalExponentialObservableWitness trajectory producer)
    (scaling : MatchedPhysicalDynamicStrengthScaling trajectory producer)
    (gapVariation : SummableRationalStepVariation
      (trajectory.toCompletedFamily producer).physicalGap)
    (strengthVariation : SummableRationalStepVariation
      (trajectory.toNormalizedStrengthLaw producer).strength)
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {existence : ContinuumYMExistence mu}
    {osGNS : MeasureLinkedOSGNSData existence}
    (projectiveOS : ProjectiveOSCorrelationHandoff
      witness.observable.toPhysicalSeparator existence osGNS
        witness.observable.physicalSampling)
    (spectralChannel :
      ProjectiveOSCorrelationHandoff.ReconstructionSpectralChannelHandoff
        projectiveOS osGNS.reconstruction)
    (exactRate : ExactRateReconstructionHandoff
      (YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.exactCertificate
        witness.observable
        (scaling.toPhysicalRateBand)
        (fullRangeLogRateCeilingOfPhysicalRateBand
          witness.observable scaling.toPhysicalRateBand))
      osGNS.reconstruction)
    (C : AFTrajectoryCertificate)
    (H : ShiftedAFTrajectoryIdentification C trajectory.coupling) :
    YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.DynamicVacuumSectorContinuumHandoff
      witness.observable
      (scaling.toPhysicalRateBand)
      (fullRangeLogRateCeilingOfPhysicalRateBand
        witness.observable scaling.toPhysicalRateBand)
      existence osGNS :=
  toContinuumHandoff_ofRescaledStrengthAndComputedCeiling
    witness scaling
    (rescaledStrengthVariationOfPhysicalGapAndStrength
      (trajectory.toNormalizedStrengthLaw producer)
      gapVariation strengthVariation)
    projectiveOS spectralChannel exactRate C H

/-- Same-carrier continuum handoff after reducing normalized-strength
variation to ray-capacity and finite-sector mass-floor streams. -/
def toContinuumHandoff_ofRayCapacityAndMassFloorAndPhysicalGapAndComputedCeiling
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (witness : PhysicalExponentialObservableWitness trajectory producer)
    (scaling : MatchedPhysicalDynamicStrengthScaling trajectory producer)
    (rayDeltaVariation : SummableRationalStepVariation
      (fun scale =>
        (((trajectory.toDynamicFamily producer).toResidualCoercivityFamily.rayCapacity
          scale).delta)))
    (massFloorVariation : SummableRationalStepVariation
      (fun scale =>
        centralPhysicalFiniteVacuumSectorUniformMassFloor
          ((trajectory.toDynamicFamily producer).toResidualCoercivityFamily.nome
            scale)
          (Q'.le_of_lt
            ((trajectory.toDynamicFamily producer).toResidualCoercivityFamily.nome_pos
              scale)) 0))
    (gapVariation : SummableRationalStepVariation
      (trajectory.toCompletedFamily producer).physicalGap)
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {existence : ContinuumYMExistence mu}
    {osGNS : MeasureLinkedOSGNSData existence}
    (projectiveOS : ProjectiveOSCorrelationHandoff
      witness.observable.toPhysicalSeparator existence osGNS
        witness.observable.physicalSampling)
    (spectralChannel :
      ProjectiveOSCorrelationHandoff.ReconstructionSpectralChannelHandoff
        projectiveOS osGNS.reconstruction)
    (exactRate : ExactRateReconstructionHandoff
      (YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.exactCertificate
        witness.observable
        (scaling.toPhysicalRateBand)
        (fullRangeLogRateCeilingOfPhysicalRateBand
          witness.observable scaling.toPhysicalRateBand))
      osGNS.reconstruction)
    (C : AFTrajectoryCertificate)
    (H : ShiftedAFTrajectoryIdentification C trajectory.coupling) :
    YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.DynamicVacuumSectorContinuumHandoff
      witness.observable
      (scaling.toPhysicalRateBand)
      (fullRangeLogRateCeilingOfPhysicalRateBand
        witness.observable scaling.toPhysicalRateBand)
      existence osGNS :=
  matchedContinuumHandoffOfRescaledStrength
    trajectory producer scaling witness.observable
    (rescaledStrengthVariationOfPhysicalGapAndStrength
      (trajectory.toNormalizedStrengthLaw producer)
      gapVariation
      (by
        let residualFamily :=
          (trajectory.toDynamicFamily producer).toResidualCoercivityFamily
        let strengthVariation := strengthVariationOfRayDeltaAndMassFloor
          residualFamily rayDeltaVariation massFloorVariation
        simpa only [residualFamily,
          MatchedPhysicalDynamicScalarTrajectory.toNormalizedStrengthLaw,
          DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.toNormalizedStrengthLaw]
          using strengthVariation))
    (fullRangeLogRateCeilingOfPhysicalRateBand
      witness.observable scaling.toPhysicalRateBand)
    projectiveOS spectralChannel exactRate C H

/-- The matched observable witness reaches the existing continuum handoff
from the same-family exact-log variation compiler.  Projective/OS semantics,
the spectral channel, and exact-rate reconstruction identification remain
explicit arguments on the identical separator and completed family. -/
def toContinuumHandoff_ofGapVariation
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (witness :
      PhysicalExponentialObservableWitness trajectory producer)
    (band : StrengthBand trajectory producer)
    (ceiling :
      FullRangeLogRateCeiling
        (YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.fullRangeRateFamily
          witness.observable))
    (gapVariation : PhysicalGapRationalVariation trajectory producer)
    (spacingTail :
      InverseSquareSpacingTail
        (trajectory.toCompletedFamily producer).transferSpacing 0)
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (existence : ContinuumYMExistence mu)
    (osGNS : MeasureLinkedOSGNSData existence)
    (projectiveOS : ProjectiveOSCorrelationHandoff
      witness.observable.toPhysicalSeparator existence osGNS
        witness.observable.physicalSampling)
    (spectralChannel :
      ProjectiveOSCorrelationHandoff.ReconstructionSpectralChannelHandoff
        projectiveOS osGNS.reconstruction)
    (exactRate : ExactRateReconstructionHandoff
      (YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.exactCertificate
        witness.observable
        ((adaptiveFamily trajectory producer).physicalRateBand band)
        ceiling)
      osGNS.reconstruction) :
    YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.DynamicVacuumSectorContinuumHandoff
      witness.observable
      ((adaptiveFamily trajectory producer).physicalRateBand band)
      ceiling existence osGNS :=
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler.DynamicVacuumSectorObservablePin.DynamicVacuumSectorContinuumHandoff.ofExactLogVariations
    gapVariation spacingTail projectiveOS spectralChannel exactRate

/-- The computed full-log ceiling removes the last independent upper-rate
input from the same-object continuum handoff.  The exact-rate reconstruction
certificate remains explicitly indexed by that computed ceiling. -/
def toContinuumHandoff_ofGapVariationAndComputedCeiling
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (witness :
      PhysicalExponentialObservableWitness trajectory producer)
    (band : StrengthBand trajectory producer)
    (gapVariation : PhysicalGapRationalVariation trajectory producer)
    (spacingTail :
      InverseSquareSpacingTail
        (trajectory.toCompletedFamily producer).transferSpacing 0)
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (existence : ContinuumYMExistence mu)
    (osGNS : MeasureLinkedOSGNSData existence)
    (projectiveOS : ProjectiveOSCorrelationHandoff
      witness.observable.toPhysicalSeparator existence osGNS
        witness.observable.physicalSampling)
    (spectralChannel :
      ProjectiveOSCorrelationHandoff.ReconstructionSpectralChannelHandoff
        projectiveOS osGNS.reconstruction)
    (exactRate : ExactRateReconstructionHandoff
      (YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.exactCertificate
        witness.observable
        ((adaptiveFamily trajectory producer).physicalRateBand band)
        (toFullRangeLogRateCeiling_ofStrengthBandComputed witness band))
      osGNS.reconstruction) :
    YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.DynamicVacuumSectorContinuumHandoff
      witness.observable
      ((adaptiveFamily trajectory producer).physicalRateBand band)
      (toFullRangeLogRateCeiling_ofStrengthBandComputed witness band)
      existence osGNS :=
  toContinuumHandoff_ofGapVariation witness band
    (toFullRangeLogRateCeiling_ofStrengthBandComputed witness band)
    gapVariation spacingTail existence osGNS projectiveOS spectralChannel
    exactRate

/-- Export the existing conditional exact-log continuum endpoint through the
matched observable/carrier indices. -/
def toContinuumYMWithExactLogGap_ofHandoff
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (witness :
      PhysicalExponentialObservableWitness trajectory producer)
    (band : StrengthBand trajectory producer)
    (ceiling :
      FullRangeLogRateCeiling
        (YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.fullRangeRateFamily
          witness.observable))
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {existence : ContinuumYMExistence mu}
    {osGNS : MeasureLinkedOSGNSData existence}
    (handoff :
      YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.DynamicVacuumSectorContinuumHandoff
        witness.observable
        ((adaptiveFamily trajectory producer).physicalRateBand band)
        ceiling existence osGNS) :
    YMGap.Continuum.PhysicalSeparatorContinuumRealization.ContinuumYMWithExactLogGap
      (YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.exactCertificate
        witness.observable
        ((adaptiveFamily trajectory producer).physicalRateBand band)
        ceiling) mu :=
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.DynamicVacuumSectorContinuumHandoff.toContinuumYMWithExactLogGap
    handoff

/-- Endpoint packaging for the computed-ceiling handoff. -/
def toContinuumYMWithExactLogGap_ofComputedHandoff
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (witness :
      PhysicalExponentialObservableWitness trajectory producer)
    (band : StrengthBand trajectory producer)
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {existence : ContinuumYMExistence mu}
    {osGNS : MeasureLinkedOSGNSData existence}
    (handoff :
      YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.DynamicVacuumSectorContinuumHandoff
        witness.observable
        ((adaptiveFamily trajectory producer).physicalRateBand band)
        (toFullRangeLogRateCeiling_ofStrengthBandComputed witness band)
        existence osGNS) :
    YMGap.Continuum.PhysicalSeparatorContinuumRealization.ContinuumYMWithExactLogGap
      (YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.exactCertificate
        witness.observable
        ((adaptiveFamily trajectory producer).physicalRateBand band)
        (toFullRangeLogRateCeiling_ofStrengthBandComputed witness band)) mu :=
  toContinuumYMWithExactLogGap_ofHandoff witness band
    (toFullRangeLogRateCeiling_ofStrengthBandComputed witness band) handoff

/-- The matched endpoint retains the existing constructive positive exact-log
mass consequence of the same handoff. -/
theorem continuumMass_posEv_ofHandoff
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (witness :
      PhysicalExponentialObservableWitness trajectory producer)
    (band : StrengthBand trajectory producer)
    (ceiling :
      FullRangeLogRateCeiling
        (YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.fullRangeRateFamily
          witness.observable))
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {existence : ContinuumYMExistence mu}
    {osGNS : MeasureLinkedOSGNSData existence}
    (handoff :
      YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.DynamicVacuumSectorContinuumHandoff
        witness.observable
        ((adaptiveFamily trajectory producer).physicalRateBand band)
        ceiling existence osGNS) :
    TuranPositivity.PosEv
      (YMGap.Continuum.PhysicalSeparatorContinuumRealization.PhysicalSeparatorContinuumRealization.endpointMass
        (toContinuumYMWithExactLogGap_ofHandoff witness band ceiling handoff)) :=
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.DynamicVacuumSectorContinuumHandoff.continuumMass_posEv
    handoff

/-- The matched endpoint retains the OS/spectral equality for the same
physically sampled gap observable. -/
theorem osGapCorr_equiv_spectral_ofHandoff
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {producer : trajectory.LocalProducer}
    (witness :
      PhysicalExponentialObservableWitness trajectory producer)
    (band : StrengthBand trajectory producer)
    (ceiling :
      FullRangeLogRateCeiling
        (YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.fullRangeRateFamily
          witness.observable))
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {existence : ContinuumYMExistence mu}
    {osGNS : MeasureLinkedOSGNSData existence}
    (handoff :
      YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.DynamicVacuumSectorContinuumHandoff
        witness.observable
        ((adaptiveFamily trajectory producer).physicalRateBand band)
        ceiling existence osGNS)
    (time : Nat) :
    CReal.Equiv
      (CReal.ofQ' (existence.os_axioms.E.E
        (handoff.projectiveOS.osConnectedTwoPoint.connectedInsertion
          handoff.projectiveOS.osConnectedTwoPoint.gapInsertion time)))
      (CReal.ofQ'
        (SpectralGap.corr osGNS.reconstruction.spec time)) :=
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.DynamicVacuumSectorContinuumHandoff.osGapCorr_equiv_spectral
    handoff time

/-! ## 6. Contract the local producer to the correlated same-edge debt seam -/

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

/-! ## 7. Correlated local debt into the continuum handoff -/

/- The producer returned by the correlated same-edge compiler is named once so
   the downstream certificate types remain visibly indexed by one completed
   carrier. -/
abbrev correlatedCapacityDebtProducer
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
        (1 : Q')) : trajectory.LocalProducer :=
  localProducer_ofCorrelatedCapacityDebt trajectory transitionStart envelope
    tailAllowance tailAllowance_pos initial_closure

/-! The exact-rate cutoff stage is exposed separately from the semantic
    projective/OS handoff. -/
def toExactRateCutoffRemoval_ofCorrelatedCapacityDebtAndPrimitiveVariations
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
    (witness : PhysicalExponentialObservableWitness trajectory
      (correlatedCapacityDebtProducer trajectory transitionStart envelope
        tailAllowance tailAllowance_pos initial_closure))
    (scaling : MatchedPhysicalDynamicStrengthScaling trajectory
      (correlatedCapacityDebtProducer trajectory transitionStart envelope
        tailAllowance tailAllowance_pos initial_closure))
    (rayDeltaVariation : SummableRationalStepVariation
      (fun scale =>
        (((trajectory.toDynamicFamily
          (correlatedCapacityDebtProducer trajectory transitionStart envelope
            tailAllowance tailAllowance_pos initial_closure)).toResidualCoercivityFamily.rayCapacity
          scale).delta)))
    (massFloorVariation : SummableRationalStepVariation
      (fun scale =>
        centralPhysicalFiniteVacuumSectorUniformMassFloor
          ((trajectory.toDynamicFamily
            (correlatedCapacityDebtProducer trajectory transitionStart envelope
              tailAllowance tailAllowance_pos initial_closure)).toResidualCoercivityFamily.nome
            scale)
          (Q'.le_of_lt
            ((trajectory.toDynamicFamily
              (correlatedCapacityDebtProducer trajectory transitionStart envelope
                tailAllowance tailAllowance_pos initial_closure)).toResidualCoercivityFamily.nome_pos
              scale)) 0))
    (gapVariation : PhysicalGapRationalVariation trajectory
      (correlatedCapacityDebtProducer trajectory transitionStart envelope
        tailAllowance tailAllowance_pos initial_closure))
    (C : AFTrajectoryCertificate)
    (H : ShiftedAFTrajectoryIdentification C trajectory.coupling) :
    ExactRateCutoffRemoval
      (YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.exactCertificate
        witness.observable scaling.toPhysicalRateBand
        (fullRangeLogRateCeilingOfPhysicalRateBand
          witness.observable scaling.toPhysicalRateBand)) :=
  toExactRateCutoffRemoval_ofRayCapacityAndMassFloorAndPhysicalGapAndComputedCeiling
    witness scaling rayDeltaVariation massFloorVariation gapVariation C H

/-! The local capacity/debt compiler can now be joined directly to the
    existing same-carrier continuum handoff.  Every analytic input not
    supplied by that local compiler remains an explicit argument, and the
    projective/OS/exact-rate fields are indexed by the very observable selected
    from the same generated producer. -/
def toContinuumHandoff_ofCorrelatedCapacityDebtAndPrimitiveVariations
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
      (correlatedCapacityDebtProducer trajectory transitionStart envelope
        tailAllowance tailAllowance_pos initial_closure))
    (normalizationDebt : MovingCubeNormalizationDebtRationalVariation trajectory
      (correlatedCapacityDebtProducer trajectory transitionStart envelope
        tailAllowance tailAllowance_pos initial_closure))
    (scaling : MatchedPhysicalDynamicStrengthScaling trajectory
      (correlatedCapacityDebtProducer trajectory transitionStart envelope
        tailAllowance tailAllowance_pos initial_closure))
    (rayDeltaVariation : SummableRationalStepVariation
      (fun scale =>
        (((trajectory.toDynamicFamily
          (correlatedCapacityDebtProducer trajectory transitionStart envelope
            tailAllowance tailAllowance_pos initial_closure)).toResidualCoercivityFamily.rayCapacity
          scale).delta)))
    (massFloorVariation : SummableRationalStepVariation
      (fun scale =>
        centralPhysicalFiniteVacuumSectorUniformMassFloor
          ((trajectory.toDynamicFamily
            (correlatedCapacityDebtProducer trajectory transitionStart envelope
              tailAllowance tailAllowance_pos initial_closure)).toResidualCoercivityFamily.nome
            scale)
          (Q'.le_of_lt
            ((trajectory.toDynamicFamily
              (correlatedCapacityDebtProducer trajectory transitionStart envelope
                tailAllowance tailAllowance_pos initial_closure)).toResidualCoercivityFamily.nome_pos
              scale)) 0))
    (gapVariation : PhysicalGapRationalVariation trajectory
      (correlatedCapacityDebtProducer trajectory transitionStart envelope
        tailAllowance tailAllowance_pos initial_closure))
    (positiveRatePower : PositiveMovingCubeRatePowerRationalVariation trajectory
      (correlatedCapacityDebtProducer trajectory transitionStart envelope
        tailAllowance tailAllowance_pos initial_closure))
    (observable : trajectory.SameObjectObservablePin
      (correlatedCapacityDebtProducer trajectory transitionStart envelope
        tailAllowance tailAllowance_pos initial_closure))
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {existence : ContinuumYMExistence mu}
    {osGNS : MeasureLinkedOSGNSData existence}
    (projectiveOS : ProjectiveOSCorrelationHandoff
      observable.toPhysicalSeparator existence osGNS observable.physicalSampling)
    (spectralChannel :
      ProjectiveOSCorrelationHandoff.ReconstructionSpectralChannelHandoff
        projectiveOS osGNS.reconstruction)
    (exactRate : ExactRateReconstructionHandoff
      (YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.exactCertificate
        observable scaling.toPhysicalRateBand
        (fullRangeLogRateCeilingOfPhysicalRateBand
          observable scaling.toPhysicalRateBand))
      osGNS.reconstruction)
    (C : AFTrajectoryCertificate)
    (H : ShiftedAFTrajectoryIdentification C trajectory.coupling) :
    YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin.DynamicVacuumSectorContinuumHandoff
      observable scaling.toPhysicalRateBand
      (fullRangeLogRateCeilingOfPhysicalRateBand
        observable scaling.toPhysicalRateBand)
      existence osGNS := by
  let producer :=
    correlatedCapacityDebtProducer trajectory transitionStart envelope
      tailAllowance tailAllowance_pos initial_closure
  let witness :
      PhysicalExponentialObservableWitness trajectory producer :=
    PhysicalExponentialObservableWitness.ofRationalVariations
      trajectory producer raw normalizationDebt scaling.toStrengthBand
      gapVariation positiveRatePower observable
  exact toContinuumHandoff_ofRayCapacityAndMassFloorAndPhysicalGapAndComputedCeiling
    witness scaling rayDeltaVariation massFloorVariation gapVariation
    projectiveOS spectralChannel exactRate C H

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
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.PhysicalExponentialObservableWitness.ofCertificate
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.PhysicalExponentialObservableWitness.ofRationalVariations
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.PhysicalExponentialObservableWitness.physicalSeparator_gapObservable_zero_pos
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.toFullRangeExactPhysicalSeparatorCertificate
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.toExactRateCutoffRemoval
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.toExactRateCutoffRemoval_ofTrajectorySpacing
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.toFullRangeExactPhysicalSeparatorCertificate_ofStrengthBand
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.toFullRangeLogRateCeiling_ofStrengthBandAndPrefix
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.toFullRangeLogRateCeiling_ofStrengthBandAndPrefix_ceiling
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.toFullRangeExactPhysicalSeparatorCertificate_ofStrengthBandAndPrefix
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.toFullRangeLogRateCeiling_ofStrengthBandComputed
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.toFullRangeExactPhysicalSeparatorCertificate_ofStrengthBandComputed
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.toExactRateCutoffRemoval_ofGapVariation
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.toExactRateCutoffRemoval_ofGapVariationAndPrefix
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.toExactRateCutoffRemoval_ofGapVariationAndComputedCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.toExactRateCutoffRemoval_ofRescaledStrengthAndComputedCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.toExactRateCutoffRemoval_ofPhysicalGapAndStrengthAndComputedCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.toExactRateCutoffRemoval_ofRayCapacityAndMassFloorAndPhysicalGapAndComputedCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.toContinuumHandoff_ofGapVariation
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.toContinuumHandoff_ofGapVariationAndComputedCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.toContinuumHandoff_ofRescaledStrengthAndComputedCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.toContinuumHandoff_ofPhysicalGapAndStrengthAndComputedCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.toContinuumHandoff_ofRayCapacityAndMassFloorAndPhysicalGapAndComputedCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.toContinuumYMWithExactLogGap_ofHandoff
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.toContinuumYMWithExactLogGap_ofComputedHandoff
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.continuumMass_posEv_ofHandoff
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.osGapCorr_equiv_spectral_ofHandoff
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.localProducer_ofCorrelatedCapacityDebt
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.toPhysicalExponentialCertificate_ofCorrelatedCapacityDebt
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.correlatedCapacityDebtProducer
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.toExactRateCutoffRemoval_ofCorrelatedCapacityDebtAndPrimitiveVariations
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicPhysicalExponentialPath.MatchedPhysicalDynamicScalarTrajectory.toContinuumHandoff_ofCorrelatedCapacityDebtAndPrimitiveVariations
