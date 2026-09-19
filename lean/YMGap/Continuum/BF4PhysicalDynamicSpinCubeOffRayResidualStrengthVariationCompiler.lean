/-
# Primitive variation compiler for the dynamic spin-ray strength

The residual local route defines its exact normalized strength by

  `(1/2 * rayCapacity.delta) * uniformSectorMassFloor`.

This module keeps those two scale-dependent factors separate and compiles
their explicit summable rational variations into variation of the exact same
strength stream.  The output can then be passed to the generic normalized
strength-to-physical-gap compiler.  Neither primitive variation input is
constructed here; the module only exposes the smallest honest producer
interface and its exact same-object consequence.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayResidualFamily
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalGapVariationCompiler
import YMGap.Continuum.SummableRationalStepVariationAlgebra

namespace YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayResidualStrengthVariationCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayResidualFamily
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayResidualFamily.DynamicSpinCubeOffRayResidualCoercivityFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalGapVariationCompiler
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorUniformMassFloor
open YMGap.Continuum.SummableRationalStepVariation
open YMGap.Continuum.SummableRationalStepVariationAlgebra

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact same-family strength variation -/

/-- Ray-delta variation and finite-sector mass-floor variation compile to
summable variation of the exact residual-family strength. -/
def strengthVariationOfRayDeltaAndMassFloor
    (family : DynamicSpinCubeOffRayResidualCoercivityFamily)
    (rayDeltaVariation :
      SummableRationalStepVariation
        (fun scale => (family.rayCapacity scale).delta))
    (massFloorVariation :
      SummableRationalStepVariation
        (fun scale =>
          centralPhysicalFiniteVacuumSectorUniformMassFloor
            (family.nome scale)
            (Q'.le_of_lt (family.nome_pos scale)) 0)) :
    SummableRationalStepVariation family.strength := by
  let scaledRayDelta := scale rayDeltaVariation
    HalfPow.half (by decide)
  have scaledRayDelta_nonnegative :
      forall scale, (0 : Q') <=
        HalfPow.half * (family.rayCapacity scale).delta := by
    intro scale
    exact Q'.mul_nonneg _ _
      (by decide)
      (Q'.le_of_lt ((family.rayCapacity scale).delta_pos))
  have massFloor_nonnegative :
      forall scale, (0 : Q') <=
        centralPhysicalFiniteVacuumSectorUniformMassFloor
          (family.nome scale)
          (Q'.le_of_lt (family.nome_pos scale)) 0 := by
    intro scale
    exact Q'.le_of_lt
      (centralPhysicalFiniteVacuumSectorUniformMassFloor_pos
        (family.nome scale)
        (Q'.le_of_lt (family.nome_pos scale)) 0)
  let productVariation := mul scaledRayDelta massFloorVariation
    scaledRayDelta_nonnegative massFloor_nonnegative
  exact ofPointwiseEqv productVariation (fun scale => by
    unfold strength cutoffTwoDirichletGluingStrength
    rfl)

/-! ## 2. Meet the physical-gap backward compiler -/

/-- The exact residual strength variation meets reciprocal-spacing variation
at the same completed family and yields its physical-gap variation. -/
def physicalGapVariationOfRayDeltaMassFloorAndReciprocalSpacing
    (family : DynamicSpinCubeOffRayResidualCoercivityFamily)
    (rayDeltaVariation :
      SummableRationalStepVariation
        (fun scale => (family.rayCapacity scale).delta))
    (massFloorVariation :
      SummableRationalStepVariation
        (fun scale =>
          centralPhysicalFiniteVacuumSectorUniformMassFloor
            (family.nome scale)
            (Q'.le_of_lt (family.nome_pos scale)) 0))
    (reciprocalSpacingVariation :
      SummableRationalStepVariation
        (fun scale =>
          Q'.recipPos
            (family.transferSpacing.spacing scale)
            (family.transferSpacing.spacing_pos scale))) :
    SummableRationalStepVariation family.toCompletedFamily.physicalGap :=
  physicalGapVariationOfNormalizedStrengthAndReciprocalSpacing
    family.toCompletedFamily family.toNormalizedStrengthLaw
    (strengthVariationOfRayDeltaAndMassFloor
      family rayDeltaVariation massFloorVariation)
    reciprocalSpacingVariation

end YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayResidualStrengthVariationCompiler

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayResidualStrengthVariationCompiler.strengthVariationOfRayDeltaAndMassFloor
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayResidualStrengthVariationCompiler.physicalGapVariationOfRayDeltaMassFloorAndReciprocalSpacing
