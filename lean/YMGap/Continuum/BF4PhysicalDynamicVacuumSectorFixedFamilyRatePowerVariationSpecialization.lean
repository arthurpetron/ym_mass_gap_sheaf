/-
# Actual normalized-stream specialization of the fixed-family rate certificate

The lightweight core proves variation for `r^(time * 2^scale)`.  This file
transports that certificate to the literal normalized moving-cube scheduled
rate stream of the concrete SU(2) geometric staging family, using only the
checked fixed-rate pin and floor-sampler identity.  It also converts the
pointwise-constant reciprocal-square normalization debt into the constructive-
real variation interface.  These scalar inputs are usable by the normalized
cutoff compiler; the file does not provide raw connected-moment variation or a
positive physical mass.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerArithmetic
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyNormalizedDebt
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationCore
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeNontrivialityCompiler
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeRationalVariationCompiler
import YMGap.Continuum.BF4PhysicalMarginalGeometricCompletedFamily
import YMGap.Continuum.SummableRationalStepVariationAlgebra
import YMGap.Constructive.CRealInnerRegularity

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletionCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovAdaptiveCompletedTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredNonzero
open YMGap.Continuum.BF4PhysicalCutoffStationarySourceTail
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerArithmetic
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyNormalizedDebt
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationCore
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeRationalVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeNontrivialityCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel
open YMGap.Continuum.BF4PhysicalMarginalGeometricCompletedFamily
open YMGap.Continuum.SummableRationalStepVariation
open YMGap.Continuum.SummableRationalStepVariationAlgebra
open YMGap.Continuum.SummableCRealStepVariation
open YMGap.Continuum.BF4PhysicalCubeCutoffUniformGap
open YMGap.Constructive.CReal

local infix:50 " ≈ " => Q'.eqv

private def fixedSquaredRate : Q' :=
  cutoffUniformRate HalfPow.half (by decide) *
    cutoffUniformRate HalfPow.half (by decide)

private theorem fixedSquaredRate_pos : (0 : Q') < fixedSquaredRate := by
  unfold fixedSquaredRate
  exact Q'.mul_pos
    (cutoffUniformRate_pos HalfPow.half (by decide))
    (cutoffUniformRate_pos HalfPow.half (by decide))

private theorem fixedSquaredRate_lt_one : fixedSquaredRate < (1 : Q') := by
  let q := cutoffUniformRate HalfPow.half (by decide)
  have hqpos : (0 : Q') < q := cutoffUniformRate_pos HalfPow.half (by decide)
  have hqone : q < (1 : Q') := cutoffUniformRate_lt_one HalfPow.half (by decide)
  have hmul : q * q < q * 1 := Q'.mul_lt_mul_of_pos_left hqpos hqone
  have hq1 : q * 1 ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv q))
      (Q'.le_of_lt hqone)
  exact YMGap.Continuum.ContinuumClosureProgram.q'_lt_of_lt_of_le hmul hq1

private theorem actual_stream_eqv_geometric
    (scale time : Nat) :
    normalizedMovingCubeSampledRatePower
        marginalHalfGeometricCompletedFamily scale time ≈
      fixedSquaredRate ^ (time * 2 ^ scale) := by
  unfold normalizedMovingCubeSampledRatePower fixedSquaredRate
  rw [marginalHalfGeometric_latticeSteps_eq]
  exact Q'.eqv_refl _

/-! ## Concrete normalization-debt input -/

/-- The reciprocal-square normalization debt of the fixed-nome family has an
explicit constructive-real variation certificate.  Its rational stream is
pointwise constant, so the conversion contributes no new analytic
assumption.  The raw same-object moment remains separate. -/
def marginalHalfGeometric_normalizationNormDebtVariation :
    MovingCubeNormalizationNormDebtVariation
      marginalHalfGeometricCompletedFamily :=
  movingCubeNormalizationNormDebtVariationOfRational
    marginalHalfGeometricCompletedFamily
    marginalHalfGeometric_normalizationNormDebtRationalVariation

/-! ## Concrete positive-time compiler input -/

def marginalHalfGeometric_positiveRatePowerVariation
    (time : Nat) (htime : 0 < time) :
    SummableRationalStepVariation
      (fun scale => normalizedMovingCubeSampledRatePower
        marginalHalfGeometricCompletedFamily scale time) := by
  exact ofPointwiseEqv
    (positiveRatePowerVariation fixedSquaredRate
      fixedSquaredRate_pos fixedSquaredRate_lt_one time htime)
    (fun scale => Q'.eqv_symm (actual_stream_eqv_geometric scale time))

def marginalHalfGeometric_ratePowerVariation :
    NormalizedMovingCubeSampledRatePowerRationalVariation
      marginalHalfGeometricCompletedFamily :=
  normalizedMovingCubeSampledRatePowerRationalVariationOfPositive
    marginalHalfGeometricCompletedFamily
    marginalHalfGeometric_positiveRatePowerVariation

/-! ## Conditional raw nontriviality is already available -/

private def marginalHalfGeometric_normalizationScaleCeiling :
    MovingCubeNormalizationScaleCeiling
      marginalHalfGeometricCompletedFamily :=
  { ceiling :=
      movingCubeNormalizationScale marginalHalfGeometricCompletedFamily 0
    ceiling_pos := movingCubeNormalizationScale_pos
      marginalHalfGeometricCompletedFamily 0
    scale_le := fun scale => by
      exact Q'.le_refl' _ }

/-- Once the raw representative/variation certificate is supplied, the
fixed-family uniform norm floor already constructs the exact raw continuum
zero-time nontriviality witness.  This closes that downstream field
conditionally without selecting a CReal representative. -/
def marginalHalfGeometric_rawContinuumNontriviality
    (raw : MovingCubeRawScheduledRepresentativeVariation
      marginalHalfGeometricCompletedFamily) :
    MovingCubeRawContinuumNontriviality
      marginalHalfGeometricCompletedFamily raw :=
  MovingCubeRawContinuumNontriviality.ofUniformNormFloor
    marginalHalfGeometric_normalizationScaleCeiling.toUniformNormFloor

/-! ## Explicit raw representatives from the actual Cauchy presentations -/

private def marginalHalfGeometricRawInitialCauchy (scale : Nat) :
    (centralPhysicalCutoffLinearSquaredSeminorm
      (marginalHalfGeometricCompletedFamily.nome_pos scale)
      (marginalHalfGeometricCompletedFamily.nome_lt_one scale) 0).Cauchy :=
  centralPhysicalVacuumSectorCylinderCauchyToGlobal
    (centralPhysicalVacuumSectorMovingCenteredCauchy
      (marginalHalfGeometricCompletedFamily.nome_pos scale)
      (marginalHalfGeometricCompletedFamily.nome_lt_one scale)
      1 0
      (centralPhysicalCutoffOneCubeIndicatorCoefficient
        (marginalHalfGeometricCompletedFamily.nome scale)
        (marginalHalfGeometricCompletedFamily.nome_pos scale)))

private def marginalHalfGeometricRawPowerCauchy (scale : Nat) : Nat →
    (centralPhysicalCutoffLinearSquaredSeminorm
      (marginalHalfGeometricCompletedFamily.nome_pos scale)
      (marginalHalfGeometricCompletedFamily.nome_lt_one scale) 0).Cauchy
  | 0 => marginalHalfGeometricRawInitialCauchy scale
  | n + 1 =>
      centralPhysicalAdaptiveMarkovMapCauchy
        (centralPhysicalDenseMarkovCauchyData
          (marginalHalfGeometricCompletedFamily.nome_pos scale)
          (marginalHalfGeometricCompletedFamily.nome_lt_one scale) 0)
        (marginalHalfGeometricRawPowerCauchy scale n)

private theorem marginalHalfGeometricRawInitialCauchy_mk (scale : Nat) :
    centralPhysicalVacuumSectorCylinderCompletionToGlobal
        ((centralPhysicalDynamicMovingCubeRCChannel
          marginalHalfGeometricCompletedFamily).vectorAt scale).1 =
      Quotient.mk
        (centralPhysicalCutoffLinearSquaredSeminorm
          (marginalHalfGeometricCompletedFamily.nome_pos scale)
          (marginalHalfGeometricCompletedFamily.nome_lt_one scale) 0).completionSetoid
        (marginalHalfGeometricRawInitialCauchy scale) := by
  rfl

private theorem marginalHalfGeometricRawPowerCauchy_mk
    (scale n : Nat) :
    centralPhysicalConcreteAdaptiveCompletedMarkovPower
        (marginalHalfGeometricCompletedFamily.nome_pos scale)
        (marginalHalfGeometricCompletedFamily.nome_lt_one scale) 0 n
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal
          ((centralPhysicalDynamicMovingCubeRCChannel
            marginalHalfGeometricCompletedFamily).vectorAt scale).1) =
      Quotient.mk
        (centralPhysicalCutoffLinearSquaredSeminorm
          (marginalHalfGeometricCompletedFamily.nome_pos scale)
          (marginalHalfGeometricCompletedFamily.nome_lt_one scale) 0).completionSetoid
        (marginalHalfGeometricRawPowerCauchy scale n) := by
  induction n with
  | zero => exact marginalHalfGeometricRawInitialCauchy_mk scale
  | succ n ih =>
      rw [centralPhysicalConcreteAdaptiveCompletedMarkovPower,
        centralPhysicalConcreteAdaptiveCompletedMarkovTransfer, ih,
        centralPhysicalAdaptiveCompletedMarkovTransfer_mk]
      rfl

/-- A CReal representative is obtained from the explicit Cauchy presentations
used to build the same moving-cube vector and its actual completed transfer
powers.  No quotient representative is selected. -/
def marginalHalfGeometricRawRepresentative (time scale : Nat) : CReal :=
  physicalCauchyPairingLimit
    (marginalHalfGeometricCompletedFamily.nome_pos scale)
    (marginalHalfGeometricCompletedFamily.nome_lt_one scale) 0
    (marginalHalfGeometricRawPowerCauchy scale
      (centralPhysicalDynamicRCLatticeSteps
        marginalHalfGeometricCompletedFamily scale time))
    (marginalHalfGeometricRawInitialCauchy scale)

/-! A proof-argument-canonical presentation of the same fixed-nome stream.
The family fields reduce to `1/2`, but their proof arguments need not be
definitionally identical across scales.  Fixing the two decidable proofs here
removes that representational noise from the remaining variation estimate. -/

private def marginalHalfGeometricRawInitialCauchyCanonical :
    (centralPhysicalCutoffLinearSquaredSeminorm
      (by decide : (0 : Q') < HalfPow.half)
      (by decide : HalfPow.half < (1 : Q')) 0).Cauchy :=
  centralPhysicalVacuumSectorCylinderCauchyToGlobal
    (centralPhysicalVacuumSectorMovingCenteredCauchy
      (by decide : (0 : Q') < HalfPow.half)
      (by decide : HalfPow.half < (1 : Q'))
      1 0
      (centralPhysicalCutoffOneCubeIndicatorCoefficient
        HalfPow.half (by decide : (0 : Q') < HalfPow.half)))

private def marginalHalfGeometricRawPowerCauchyCanonical : Nat →
    (centralPhysicalCutoffLinearSquaredSeminorm
      (by decide : (0 : Q') < HalfPow.half)
      (by decide : HalfPow.half < (1 : Q')) 0).Cauchy
  | 0 => marginalHalfGeometricRawInitialCauchyCanonical
  | n + 1 =>
      centralPhysicalAdaptiveMarkovMapCauchy
        (centralPhysicalDenseMarkovCauchyData
          (by decide : (0 : Q') < HalfPow.half)
          (by decide : HalfPow.half < (1 : Q')) 0)
        (marginalHalfGeometricRawPowerCauchyCanonical n)

def marginalHalfGeometricRawRepresentativeCanonical
    (time scale : Nat) : CReal :=
  physicalCauchyPairingLimit
    (by decide : (0 : Q') < HalfPow.half)
    (by decide : HalfPow.half < (1 : Q')) 0
    (marginalHalfGeometricRawPowerCauchyCanonical
      (time * 2 ^ scale))
    marginalHalfGeometricRawInitialCauchyCanonical

private theorem marginalHalfGeometricRawInitialCauchyCanonical_mk
    (scale : Nat) :
    centralPhysicalVacuumSectorCylinderCompletionToGlobal
        ((centralPhysicalDynamicMovingCubeRCChannel
          marginalHalfGeometricCompletedFamily).vectorAt scale).1 =
      Quotient.mk
        (centralPhysicalCutoffLinearSquaredSeminorm
          (by decide : (0 : Q') < HalfPow.half)
          (by decide : HalfPow.half < (1 : Q')) 0).completionSetoid
        marginalHalfGeometricRawInitialCauchyCanonical := by
  rfl

private theorem marginalHalfGeometricRawInitialCauchyCanonical_mk_family
    (scale : Nat) :
    centralPhysicalVacuumSectorCylinderCompletionToGlobal
        ((centralPhysicalDynamicMovingCubeRCChannel
          marginalHalfGeometricCompletedFamily).vectorAt scale).1 =
      Quotient.mk
        (centralPhysicalCutoffLinearSquaredSeminorm
          (marginalHalfGeometricCompletedFamily.nome_pos scale)
          (marginalHalfGeometricCompletedFamily.nome_lt_one scale) 0).completionSetoid
        marginalHalfGeometricRawInitialCauchyCanonical := by
  rfl

private theorem marginalHalfGeometricRawPowerCauchyCanonical_mk
    (scale n : Nat) :
    centralPhysicalConcreteAdaptiveCompletedMarkovPower
        (by decide : (0 : Q') < HalfPow.half)
        (by decide : HalfPow.half < (1 : Q')) 0 n
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal
          ((centralPhysicalDynamicMovingCubeRCChannel
            marginalHalfGeometricCompletedFamily).vectorAt scale).1) =
      Quotient.mk
        (centralPhysicalCutoffLinearSquaredSeminorm
          (by decide : (0 : Q') < HalfPow.half)
          (by decide : HalfPow.half < (1 : Q')) 0).completionSetoid
        (marginalHalfGeometricRawPowerCauchyCanonical n) := by
  induction n with
  | zero => exact marginalHalfGeometricRawInitialCauchyCanonical_mk scale
  | succ n ih =>
      rw [centralPhysicalConcreteAdaptiveCompletedMarkovPower,
        centralPhysicalConcreteAdaptiveCompletedMarkovTransfer, ih,
        centralPhysicalAdaptiveCompletedMarkovTransfer_mk]
      rfl

private theorem marginalHalfGeometricGlobalProofs_eq
    (scale n : Nat) :
    centralPhysicalCutoffCompletedInner
        (marginalHalfGeometricCompletedFamily.nome_pos scale)
        (marginalHalfGeometricCompletedFamily.nome_lt_one scale) 0
        (centralPhysicalConcreteAdaptiveCompletedMarkovPower
          (marginalHalfGeometricCompletedFamily.nome_pos scale)
          (marginalHalfGeometricCompletedFamily.nome_lt_one scale) 0 n
          (centralPhysicalVacuumSectorCylinderCompletionToGlobal
            ((centralPhysicalDynamicMovingCubeRCChannel
              marginalHalfGeometricCompletedFamily).vectorAt scale).1))
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal
          ((centralPhysicalDynamicMovingCubeRCChannel
            marginalHalfGeometricCompletedFamily).vectorAt scale).1) =
      centralPhysicalCutoffCompletedInner
        (by decide : (0 : Q') < HalfPow.half)
        (by decide : HalfPow.half < (1 : Q')) 0
        (centralPhysicalConcreteAdaptiveCompletedMarkovPower
          (by decide : (0 : Q') < HalfPow.half)
          (by decide : HalfPow.half < (1 : Q')) 0 n
          (centralPhysicalVacuumSectorCylinderCompletionToGlobal
            ((centralPhysicalDynamicMovingCubeRCChannel
              marginalHalfGeometricCompletedFamily).vectorAt scale).1))
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal
          ((centralPhysicalDynamicMovingCubeRCChannel
            marginalHalfGeometricCompletedFamily).vectorAt scale).1) := by
  rfl

theorem marginalHalfGeometricRawRepresentativeCanonical_represents
    (time scale : Nat) :
    Quotient.mk CReal.crealSetoid
        (marginalHalfGeometricRawRepresentativeCanonical time scale) =
      sampledConnectedAutocorrelation
        (centralPhysicalDynamicMovingCubeRCChannel
          marginalHalfGeometricCompletedFamily) scale time := by
  rw [sampledConnectedAutocorrelation_eq_global]
  rw [marginalHalfGeometricGlobalProofs_eq]
  unfold marginalHalfGeometricRawRepresentativeCanonical
  rw [marginalHalfGeometric_latticeSteps_eq,
    marginalHalfGeometricRawPowerCauchyCanonical_mk]
  have hinit := marginalHalfGeometricRawInitialCauchyCanonical_mk_family scale
  have hinner := congrArg
    (fun z => centralPhysicalCutoffCompletedInner
      (marginalHalfGeometricCompletedFamily.nome_pos scale)
      (marginalHalfGeometricCompletedFamily.nome_lt_one scale) 0
      (Quotient.mk
        (centralPhysicalCutoffLinearSquaredSeminorm
          (marginalHalfGeometricCompletedFamily.nome_pos scale)
          (marginalHalfGeometricCompletedFamily.nome_lt_one scale) 0).completionSetoid
          (marginalHalfGeometricRawPowerCauchyCanonical
          (time * 2 ^ scale))) z) hinit
  have hinner' :
      centralPhysicalCutoffCompletedInner
          (marginalHalfGeometricCompletedFamily.nome_pos scale)
          (marginalHalfGeometricCompletedFamily.nome_lt_one scale) 0
          (Quotient.mk
            (centralPhysicalCutoffLinearSquaredSeminorm
              (marginalHalfGeometricCompletedFamily.nome_pos scale)
              (marginalHalfGeometricCompletedFamily.nome_lt_one scale) 0).completionSetoid
            (marginalHalfGeometricRawPowerCauchyCanonical
              (time * 2 ^ scale)))
          (centralPhysicalVacuumSectorCylinderCompletionToGlobal
            ((centralPhysicalDynamicMovingCubeRCChannel
              marginalHalfGeometricCompletedFamily).vectorAt scale).1) =
        centralPhysicalCutoffCompletedInner
          (marginalHalfGeometricCompletedFamily.nome_pos scale)
          (marginalHalfGeometricCompletedFamily.nome_lt_one scale) 0
          (Quotient.mk
            (centralPhysicalCutoffLinearSquaredSeminorm
              (marginalHalfGeometricCompletedFamily.nome_pos scale)
              (marginalHalfGeometricCompletedFamily.nome_lt_one scale) 0).completionSetoid
            (marginalHalfGeometricRawPowerCauchyCanonical
              (time * 2 ^ scale)))
          (Quotient.mk
            (centralPhysicalCutoffLinearSquaredSeminorm
              (marginalHalfGeometricCompletedFamily.nome_pos scale)
              (marginalHalfGeometricCompletedFamily.nome_lt_one scale) 0).completionSetoid
            marginalHalfGeometricRawInitialCauchyCanonical) := by
    exact hinner
  calc
    Quotient.mk CReal.crealSetoid
        (physicalCauchyPairingLimit
          (by decide : (0 : Q') < HalfPow.half)
          (by decide : HalfPow.half < (1 : Q')) 0
          (marginalHalfGeometricRawPowerCauchyCanonical
            (time * 2 ^ scale))
          marginalHalfGeometricRawInitialCauchyCanonical) =
      centralPhysicalCutoffCompletedInner
        (by decide : (0 : Q') < HalfPow.half)
        (by decide : HalfPow.half < (1 : Q')) 0
        (Quotient.mk
          (centralPhysicalCutoffLinearSquaredSeminorm
            (by decide : (0 : Q') < HalfPow.half)
            (by decide : HalfPow.half < (1 : Q')) 0).completionSetoid
          (marginalHalfGeometricRawPowerCauchyCanonical
            (time * 2 ^ scale)))
        (Quotient.mk
          (centralPhysicalCutoffLinearSquaredSeminorm
            (by decide : (0 : Q') < HalfPow.half)
            (by decide : HalfPow.half < (1 : Q')) 0).completionSetoid
          marginalHalfGeometricRawInitialCauchyCanonical) := by
            rfl
    _ = centralPhysicalCutoffCompletedInner
        (marginalHalfGeometricCompletedFamily.nome_pos scale)
        (marginalHalfGeometricCompletedFamily.nome_lt_one scale) 0
        (Quotient.mk
          (centralPhysicalCutoffLinearSquaredSeminorm
            (marginalHalfGeometricCompletedFamily.nome_pos scale)
            (marginalHalfGeometricCompletedFamily.nome_lt_one scale) 0).completionSetoid
          (marginalHalfGeometricRawPowerCauchyCanonical
            (time * 2 ^ scale)))
            (centralPhysicalVacuumSectorCylinderCompletionToGlobal
              ((centralPhysicalDynamicMovingCubeRCChannel
                marginalHalfGeometricCompletedFamily).vectorAt scale).1) := by
            exact hinner'.symm

/-! The fixed-family squared decay is available directly on the canonical
CReal representative, before any future square-root or variation bridge.
This is the same-object estimate rewritten from the quotient channel; no
representative is selected after the fact. -/
theorem marginalHalfGeometricRawRepresentativeCanonical_sq_decay
    (time scale : Nat) :
    CReal.leEv
      (CReal.mul
        (marginalHalfGeometricRawRepresentativeCanonical time scale)
        (marginalHalfGeometricRawRepresentativeCanonical time scale))
      (CReal.mul
      (CReal.mul
        (CReal.ofQ' (fixedSquaredRate ^ (time * 2 ^ scale)))
          (marginalHalfGeometricRawRepresentativeCanonical 0 scale))
        (marginalHalfGeometricRawRepresentativeCanonical 0 scale)) := by
  have hdecay := sampledConnectedAutocorrelationSq_decay
    (centralPhysicalDynamicMovingCubeRCChannel
      marginalHalfGeometricCompletedFamily) scale time
  have hrc : CReal.RCle
      (Quotient.mk CReal.crealSetoid
        (CReal.mul
          (marginalHalfGeometricRawRepresentativeCanonical time scale)
          (marginalHalfGeometricRawRepresentativeCanonical time scale)))
      (Quotient.mk CReal.crealSetoid
        (CReal.mul
          (CReal.mul
            (CReal.ofQ' (fixedSquaredRate ^ (time * 2 ^ scale)))
            (marginalHalfGeometricRawRepresentativeCanonical 0 scale))
          (marginalHalfGeometricRawRepresentativeCanonical 0 scale))) := by
    rw [← CReal.RCmul_mk, ← CReal.RCmul_mk, ← CReal.RCscale_mk]
    rw [marginalHalfGeometricRawRepresentativeCanonical_represents time scale,
      marginalHalfGeometricRawRepresentativeCanonical_represents 0 scale]
    rw [← sampledConnectedAutocorrelation_zero_eq_normSq] at hdecay
    simpa [sampledConnectedAutocorrelationSq,
      sampledConnectedAutocorrelation,
      marginalHalfGeometric_latticeSteps_eq,
      marginalHalfGeometricCompletedFamily_rate,
      fixedSquaredRate] using hdecay
  exact hrc

theorem marginalHalfGeometricRawRepresentativeCanonical_zero_time_const
    (scale : Nat) :
    marginalHalfGeometricRawRepresentativeCanonical 0 scale =
      marginalHalfGeometricRawRepresentativeCanonical 0 0 := by
  unfold marginalHalfGeometricRawRepresentativeCanonical
  simp [marginalHalfGeometricRawPowerCauchyCanonical]

private def completeLimitFromRate_innerRegularity
    (s : Nat -> CReal) (M : Q' -> Nat) (reg : Nat -> Q' -> Nat)
    (hreg : CReal.RegPred s reg)
    (hb : CReal.LeRatBound s M) :
    CReal.InnerRegularity
      (CReal.completeLimitFromRate s M reg hreg hb) where
  rate := fun epsilon =>
    (HalfPow.half * (HalfPow.half * epsilon)).den
  regular := by
    intro epsilon hepsilon p q hp hq
    rcases Nat.le_total p q with hpq | hqp
    · have h := CReal.diagSeqR_directed s M reg hreg hb
        epsilon hepsilon p q hpq hp
      simpa only [CReal.completeLimitFromRate_approx] using h
    · have h := CReal.diagSeqR_directed s M reg hreg hb
        epsilon hepsilon q p hqp hq
      have hs := by
        simpa only [CReal.completeLimitFromRate_approx] using h
      exact ⟨hs.2, hs.1⟩

private def marginalHalfGeometricRawCanonicalZeroInnerRegularity :
    CReal.InnerRegularity
      (marginalHalfGeometricRawRepresentativeCanonical 0 0) := by
  unfold marginalHalfGeometricRawRepresentativeCanonical
  simp only [marginalHalfGeometricRawPowerCauchyCanonical]
  exact completeLimitFromRate_innerRegularity
    (physicalCauchyPairingSeq
      (by decide : (0 : Q') < HalfPow.half)
      (by decide : HalfPow.half < (1 : Q')) 0
      marginalHalfGeometricRawInitialCauchyCanonical
      marginalHalfGeometricRawInitialCauchyCanonical)
    (fun epsilon =>
      physicalCauchyPairRateNat
        (by decide : (0 : Q') < HalfPow.half)
        (by decide : HalfPow.half < (1 : Q')) 0
        marginalHalfGeometricRawInitialCauchyCanonical
        marginalHalfGeometricRawInitialCauchyCanonical epsilon.den)
    (physicalCauchyPairingInnerRate
      (by decide : (0 : Q') < HalfPow.half)
      (by decide : HalfPow.half < (1 : Q')) 0
      marginalHalfGeometricRawInitialCauchyCanonical
      marginalHalfGeometricRawInitialCauchyCanonical)
    (physicalCauchyPairingSeq_RegPred
      (by decide : (0 : Q') < HalfPow.half)
      (by decide : HalfPow.half < (1 : Q')) 0
      marginalHalfGeometricRawInitialCauchyCanonical
      marginalHalfGeometricRawInitialCauchyCanonical)
    (physicalCauchyPairingSeq_LeRatBound
      (by decide : (0 : Q') < HalfPow.half)
      (by decide : HalfPow.half < (1 : Q')) 0
      marginalHalfGeometricRawInitialCauchyCanonical
      marginalHalfGeometricRawInitialCauchyCanonical)

def marginalHalfGeometricRawCanonicalZeroTimeVariation :
    SummableCRealStepVariation
      (fun scale => marginalHalfGeometricRawRepresentativeCanonical 0 scale) where
  variation := fun _ => 0
  variation_nonnegative := fun _ => Q'.le_refl' 0
  tailRate := fun _ => 0
  tailRate_antitone := by
    intro epsilon delta hdelta hle
    exact Nat.le_refl 0
  tailBound := by
    intro epsilon hepsilon start hstart length
    rw [RationalTail.finSum_zero_seq]
    exact Q'.le_of_lt hepsilon
  innerRate := fun _ epsilon =>
    marginalHalfGeometricRawCanonicalZeroInnerRegularity.rate epsilon
  innerRegular := by
    intro scale epsilon hepsilon p q hp hq
    have h := marginalHalfGeometricRawCanonicalZeroInnerRegularity.regular
      epsilon hepsilon p q hp hq
    rw [marginalHalfGeometricRawRepresentativeCanonical_zero_time_const scale]
    exact h
  stepBound := by
    intro scale k
    rw [marginalHalfGeometricRawRepresentativeCanonical_zero_time_const scale,
      marginalHalfGeometricRawRepresentativeCanonical_zero_time_const (scale + 1)]
    exact ⟨Q'.add_le_self_of_nonneg _ 0 (Q'.le_refl' 0),
      Q'.add_le_self_of_nonneg _ 0 (Q'.le_refl' 0)⟩

/-! The canonical stream is now ready for the all-time variation input.  The
zero-time slice is inhabited explicitly; positive-time cross-scale variation
remains the sole missing field.  We expose that split in the type itself so
the remaining certificate cannot accidentally re-prove (or silently assume)
the already-closed time-zero case. -/

structure MarginalHalfGeometricRawRepresentativeCanonicalVariation : Type 1 where
  variation : forall time,
    SummableCRealStepVariation
      (fun scale => marginalHalfGeometricRawRepresentativeCanonical time scale)

/-! Positive-time cross-scale variation is the only missing raw input.  The
time-zero slice is deliberately absent: it is supplied by
`marginalHalfGeometricRawCanonicalZeroTimeVariation` below. -/
structure MarginalHalfGeometricRawRepresentativeCanonicalPositiveTimeVariation : Type 1 where
  variation : forall (time : Nat), 0 < time ->
    SummableCRealStepVariation
      (fun scale => marginalHalfGeometricRawRepresentativeCanonical time scale)

/-! Reinsert the already-proved zero-time slice, yielding the all-time
variation object consumed by the normalized moving-cube compiler. -/
def MarginalHalfGeometricRawRepresentativeCanonicalPositiveTimeVariation.toAllTime
    (data : MarginalHalfGeometricRawRepresentativeCanonicalPositiveTimeVariation) :
    MarginalHalfGeometricRawRepresentativeCanonicalVariation where
  variation := by
    intro time
    cases time with
    | zero => exact marginalHalfGeometricRawCanonicalZeroTimeVariation
    | succ n => exact data.variation (n + 1) (Nat.succ_pos n)

def MarginalHalfGeometricRawRepresentativeCanonicalVariation.toRawScheduledVariation
    (data : MarginalHalfGeometricRawRepresentativeCanonicalVariation) :
    MovingCubeRawScheduledRepresentativeVariation
      marginalHalfGeometricCompletedFamily where
  representative := fun time scale =>
    marginalHalfGeometricRawRepresentativeCanonical time scale
  represents := fun time scale =>
    marginalHalfGeometricRawRepresentativeCanonical_represents time scale
  variation := data.variation

theorem marginalHalfGeometricRawRepresentative_represents
    (time scale : Nat) :
    Quotient.mk CReal.crealSetoid
        (marginalHalfGeometricRawRepresentative time scale) =
      sampledConnectedAutocorrelation
        (centralPhysicalDynamicMovingCubeRCChannel
          marginalHalfGeometricCompletedFamily) scale time := by
  rw [sampledConnectedAutocorrelation_eq_global]
  unfold marginalHalfGeometricRawRepresentative
  rw [marginalHalfGeometricRawPowerCauchy_mk,
    marginalHalfGeometricRawInitialCauchy_mk,
    centralPhysicalCutoffCompletedInner_mk]
  rfl

/-! The exact representative has now been constructed; only its summable
cross-scale variation remains to be supplied. -/

structure MarginalHalfGeometricRawRepresentativeVariation : Type 1 where
  variation : forall time,
    SummableCRealStepVariation
      (fun scale => marginalHalfGeometricRawRepresentative time scale)

def MarginalHalfGeometricRawRepresentativeVariation.toRawScheduledVariation
    (data : MarginalHalfGeometricRawRepresentativeVariation) :
    MovingCubeRawScheduledRepresentativeVariation
      marginalHalfGeometricCompletedFamily where
  representative := fun time scale =>
    marginalHalfGeometricRawRepresentative time scale
  represents := fun time scale =>
    marginalHalfGeometricRawRepresentative_represents time scale
  variation := data.variation

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.marginalHalfGeometric_normalizationNormDebtVariation
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.marginalHalfGeometric_positiveRatePowerVariation
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.marginalHalfGeometric_ratePowerVariation
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.marginalHalfGeometric_rawContinuumNontriviality
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.marginalHalfGeometricRawRepresentative_represents
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.MarginalHalfGeometricRawRepresentativeVariation.toRawScheduledVariation
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.marginalHalfGeometricRawRepresentativeCanonical_represents
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.marginalHalfGeometricRawCanonicalZeroTimeVariation
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.marginalHalfGeometricRawRepresentativeCanonical_sq_decay
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.MarginalHalfGeometricRawRepresentativeCanonicalPositiveTimeVariation.toAllTime
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.MarginalHalfGeometricRawRepresentativeCanonicalVariation.toRawScheduledVariation
