/-
# Fixed-family reciprocal-scale ceiling

The inhabited `w = 1/2` geometric family keeps the nome fixed at every
cutoff.  Its reciprocal moving-cube normalization scale is therefore one
constant rational stream.  This file packages that fact as the generic
`MovingCubeNormalizationScaleCeiling` consumed by the raw nontriviality and
normalization-debt routes.

The resulting floor and debt bounds are finite-family consequences only.  No
raw representative variation, positive-time rate limit, physical scaling,
continuum passage, OS/QFT reconstruction, or Clay conclusion is asserted.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeNontrivialityCompiler
import YMGap.Continuum.BF4PhysicalMarginalGeometricCompletedFamily

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyNormalizationCeiling

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeNontrivialityCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel
open YMGap.Continuum.BF4PhysicalMarginalGeometricCompletedFamily

/-- The reciprocal normalization scale is definitionally constant along the
fixed-nome geometric family. -/
theorem marginalHalfGeometric_normalizationScale_eq (scale : Nat) :
    movingCubeNormalizationScale marginalHalfGeometricCompletedFamily scale =
      movingCubeNormalizationScale marginalHalfGeometricCompletedFamily 0 := by
  rfl

/-- A global rational ceiling for the exact reciprocal normalization scale of
the fixed-nome geometric family. -/
def marginalHalfGeometric_normalizationScaleCeiling :
    MovingCubeNormalizationScaleCeiling marginalHalfGeometricCompletedFamily :=
  { ceiling :=
      movingCubeNormalizationScale marginalHalfGeometricCompletedFamily 0
    ceiling_pos := movingCubeNormalizationScale_pos
      marginalHalfGeometricCompletedFamily 0
    scale_le := fun scale => by
      rw [marginalHalfGeometric_normalizationScale_eq scale]
      exact Q'.le_refl' _ }

/-- The ceiling packages a cutoff-uniform positive floor for the literal raw
moving-cube channel. -/
def marginalHalfGeometric_normalizationScaleCeiling_uniformNormFloor :
    DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel
        marginalHalfGeometricCompletedFamily) :=
  marginalHalfGeometric_normalizationScaleCeiling.toUniformNormFloor

/-- The same ceiling bounds the exact fourth-power normalization debt at every
geometric cutoff. -/
theorem marginalHalfGeometric_correlationSqDebt_le_ceiling_fourth
    (scale : Nat) :
    movingCubeNormalizationCorrelationSqDebt
        marginalHalfGeometricCompletedFamily scale ≤
      (marginalHalfGeometric_normalizationScaleCeiling.ceiling *
        marginalHalfGeometric_normalizationScaleCeiling.ceiling) *
        (marginalHalfGeometric_normalizationScaleCeiling.ceiling *
          marginalHalfGeometric_normalizationScaleCeiling.ceiling) :=
  marginalHalfGeometric_normalizationScaleCeiling.correlationSqDebt_le_ceiling_fourth
    scale

#print axioms marginalHalfGeometric_normalizationScale_eq
#print axioms marginalHalfGeometric_normalizationScaleCeiling
#print axioms marginalHalfGeometric_normalizationScaleCeiling_uniformNormFloor
#print axioms marginalHalfGeometric_correlationSqDebt_le_ceiling_fourth

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyNormalizationCeiling
