/-
# Constant normalization debt in the fixed-nome geometric family

The moving-cube normalization floor depends on the nome.  In the inhabited
geometric staging family that nome is exactly `1/2` at every scale, so the
reciprocal-square debt is one constant rational stream.  Its summable
variation therefore has the explicit zero witness.  This supplies the debt
input to the normalized same-object cutoff compiler without asserting a raw
representative limit or a physical rate.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel
import YMGap.Continuum.BF4PhysicalMarginalGeometricCompletedFamily

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyNormalizedDebt

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel
open YMGap.Continuum.BF4PhysicalMarginalGeometricCompletedFamily
open YMGap.Continuum.SummableRationalStepVariation

/-- The exact reciprocal-square debt is constant across the fixed-nome
geometric family's cutoff scales. -/
theorem marginalHalfGeometric_normalizationNormDebt_eq (scale : Nat) :
    movingCubeNormalizationNormDebt marginalHalfGeometricCompletedFamily scale =
      movingCubeNormalizationNormDebt marginalHalfGeometricCompletedFamily 0 := by
  rfl

/-- Zero rational step variation for the actual normalized moving-cube debt
of the fixed-nome geometric family. -/
def marginalHalfGeometric_normalizationNormDebtRationalVariation :
    SummableRationalStepVariation
      (fun scale => movingCubeNormalizationNormDebt
        marginalHalfGeometricCompletedFamily scale) :=
  SummableRationalStepVariation.ofPointwiseEqvConstant
    (fun scale =>
      movingCubeNormalizationNormDebt marginalHalfGeometricCompletedFamily scale)
    (movingCubeNormalizationNormDebt marginalHalfGeometricCompletedFamily 0)
    (fun scale => by
      change Q'.eqv
        (movingCubeNormalizationNormDebt
          marginalHalfGeometricCompletedFamily scale)
        (movingCubeNormalizationNormDebt
          marginalHalfGeometricCompletedFamily 0)
      rw [marginalHalfGeometric_normalizationNormDebt_eq scale]
      exact Q'.eqv_refl _)

#print axioms marginalHalfGeometric_normalizationNormDebt_eq
#print axioms marginalHalfGeometric_normalizationNormDebtRationalVariation

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyNormalizedDebt
