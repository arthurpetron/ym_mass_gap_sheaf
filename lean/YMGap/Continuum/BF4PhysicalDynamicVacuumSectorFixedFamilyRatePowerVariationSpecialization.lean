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
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeRationalVariationCompiler
import YMGap.Continuum.BF4PhysicalMarginalGeometricCompletedFamily
import YMGap.Continuum.SummableRationalStepVariationAlgebra

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerArithmetic
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyNormalizedDebt
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationCore
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeRationalVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler
open YMGap.Continuum.BF4PhysicalMarginalGeometricCompletedFamily
open YMGap.Continuum.SummableRationalStepVariation
open YMGap.Continuum.SummableRationalStepVariationAlgebra
open YMGap.Continuum.BF4PhysicalCubeCutoffUniformGap

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

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.marginalHalfGeometric_normalizationNormDebtVariation
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.marginalHalfGeometric_positiveRatePowerVariation
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerVariationSpecialization.marginalHalfGeometric_ratePowerVariation
