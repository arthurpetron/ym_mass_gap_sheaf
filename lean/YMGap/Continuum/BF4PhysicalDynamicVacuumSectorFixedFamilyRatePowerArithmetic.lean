/-
# Arithmetic of the fixed-family physical sampler

The fixed `w = 1/2` staging family uses the exact spacing `(1/2)^scale`.
This file exposes the corresponding floor-sampler index as the literal
dyadic count `time * 2^scale`.  It is an arithmetic input for a later
positive-time rate-power variation proof; no rate limit is claimed here.
-/

import YMGap.Constructive.DyadicTimeRationals
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel
import YMGap.Continuum.BF4PhysicalMarginalGeometricCompletedFamily

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerArithmetic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.DyadicTimeRationals
open YMGap.Continuum.PhysicalSeparationSamplingOfSpacingToZero
open YMGap.Continuum.BF4PhysicalCanonicalAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel
open YMGap.Continuum.BF4PhysicalMarginalGeometricCompletedFamily

/-- The exact floor sampler for the geometric spacing is the dyadic count. -/
theorem marginalHalfGeometric_latticeSteps_eq (scale time : Nat) :
    centralPhysicalDynamicRCLatticeSteps
        marginalHalfGeometricCompletedFamily scale time =
      time * 2 ^ scale := by
  unfold centralPhysicalDynamicRCLatticeSteps
    centralPhysicalDynamicRCSampling
    physicalSeparationSamplingOfSpacingToZero
    floorLatticeSteps
    marginalHalfGeometricCompletedFamily
    canonicalAFGeometricPhysicalSpacing
    canonicalAFGeometricSpacing
  change (time * (HalfPow.half ^ scale).den) /
      (HalfPow.half ^ scale).num.toNat = time * 2 ^ scale
  have hnum : (HalfPow.half ^ scale).num.toNat = 1 := by
    rw [half_power_num]
    decide
  have hden : (HalfPow.half ^ scale).den = 2 ^ scale := by
    exact_mod_cast half_power_den scale
  rw [hnum, hden]
  simp

#print axioms marginalHalfGeometric_latticeSteps_eq

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorFixedFamilyRatePowerArithmetic
