/-
# Uniform finite-family norm floor for the moving-cube channel

The dynamic scheduled-channel interface asks for a scale-uniform positive
floor.  The fixed-`w = 1/2` geometric staging family has a genuinely constant
nome, so its existing coordinate-floor witness can be reused without any
limit argument.  This closes only that finite-family nontriviality input; the
scheduled representative limit and the physical-rate/continuum joins remain
explicit.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel
import YMGap.Continuum.BF4PhysicalMarginalGeometricCompletedFamily

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorUniformNormFloorSpecialization

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredNonzero
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel
open YMGap.Continuum.BF4PhysicalMarginalGeometricCompletedFamily

/-- The fixed-`w = 1/2` geometric family has a uniform rational floor for its
literal moving-cube completed norm square. -/
def marginalHalfGeometricMovingCubeUniformRCNormFloor :
    DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel
        marginalHalfGeometricCompletedFamily) where
  floor := centralPhysicalVacuumSectorCoordinateFloor
    HalfPow.half (by decide) 1 0
  floor_pos := centralPhysicalVacuumSectorCoordinateFloor_pos
    HalfPow.half (by decide) 1 0
  floor_le := fun scale => by
    exact (centralPhysicalDynamicMovingCubeRCChannel
      marginalHalfGeometricCompletedFamily).normFloor_le scale

/-- The scheduled zero-time same-object autocorrelation retains the explicit
uniform floor at every geometric scale. -/
theorem marginalHalfGeometricMovingCube_uniform_floor_le_zeroTime
    (scale : Nat) :
    CReal.RCle
      (Quotient.mk CReal.crealSetoid
        (CReal.ofQ'
          (centralPhysicalVacuumSectorCoordinateFloor
            HalfPow.half (by decide) 1 0)))
      (sampledConnectedAutocorrelation
        (centralPhysicalDynamicMovingCubeRCChannel
          marginalHalfGeometricCompletedFamily) scale 0) := by
  rw [sampledConnectedAutocorrelation_zero_eq_normSq]
  exact marginalHalfGeometricMovingCubeUniformRCNormFloor.floor_le scale

#print axioms marginalHalfGeometricMovingCubeUniformRCNormFloor
#print axioms marginalHalfGeometricMovingCube_uniform_floor_le_zeroTime

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorUniformNormFloorSpecialization
