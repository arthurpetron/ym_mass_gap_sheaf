/-
# A concrete dynamic ray-capacity trajectory at the strong-coupling anchor

The canonical AF scalar compiler leaves two dependent local analytic fields:
a cofinal spin-ray capacity at every scale and an adaptive conditional
transition product for that exact capacity.  The first field can already be
inhabited on a genuine, but deliberately narrower, trajectory.

This module keeps the nome fixed at the proved strong-coupling anchor
`1/400`, pairs it with the already constructed geometric physical spacing,
and uses the existing selected-row theorem to supply the same positive
cofinal ray capacity at every scale.  Thus the anchor/geometric trajectory
has all scalar data and its scale-indexed ray capacity.  A one-field extension
then asks only for the adaptive transition product and losslessly compiles it
to the existing completed dynamic family.

The fixed anchor is not the canonical AF nome trajectory and is not identified
with an actual four-dimensional grouped block evolution.  The transition-
product extension is not inhabited here.  Hence there is no physical dynamic
family, same-observable limit, completed spectral gap, continuum Yang--Mills
theory, or Clay conclusion.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4CentralSpinCubeUniformRayCapacity
import YMGap.Continuum.BF4PhysicalCanonicalAFDynamicFamilyCompiler

namespace YMGap.Continuum.BF4PhysicalAnchorDynamicRayCapacityCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CentralSpinCubeUniformRayCapacity
open YMGap.Continuum.BF4PhysicalCanonicalAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Split ray capacity from its dependent transition product -/

/-- A scale-indexed cofinal ray capacity over an already fixed scalar
trajectory.  Its proof index uses exactly the positivity witness stored by
that trajectory. -/
structure DynamicSpinCubeOffRayAdaptiveRayCapacityProducer
    (trajectory : DynamicSpinCubeOffRayAdaptiveScalarTrajectory) : Type 1 where
  rayCapacity : forall scale,
    FixedNomeCofinalSpinCubeRayCapacity (trajectory.nome_pos scale)

/-- The sole remaining local field once a scale-indexed ray capacity has been
chosen: an adaptive conditional transition product indexed by that exact
capacity at every scale. -/
structure DynamicSpinCubeOffRayAdaptiveTransitionProductExtension
    {trajectory : DynamicSpinCubeOffRayAdaptiveScalarTrajectory}
    (capacityProducer :
      DynamicSpinCubeOffRayAdaptiveRayCapacityProducer trajectory) : Type 1 where
  transitionProduct : forall scale,
    FixedNomeCofinalSpinCubeOffRayResidualAdaptiveConditionalTransitionProduct
      (trajectory.nome_pos scale) (capacityProducer.rayCapacity scale)

namespace DynamicSpinCubeOffRayAdaptiveTransitionProductExtension

/-- Reassemble a capacity producer and its one-field extension into the exact
two-field local producer expected by the scalar compiler. -/
def toLocalProducer
    {trajectory : DynamicSpinCubeOffRayAdaptiveScalarTrajectory}
    {capacityProducer :
      DynamicSpinCubeOffRayAdaptiveRayCapacityProducer trajectory}
    (extension :
      DynamicSpinCubeOffRayAdaptiveTransitionProductExtension
        capacityProducer) :
    DynamicSpinCubeOffRayAdaptiveLocalProducer trajectory where
  rayCapacity := capacityProducer.rayCapacity
  transitionProduct := extension.transitionProduct

/-- Compile the same indices to the existing seven-field dynamic family. -/
def toDynamicFamily
    {trajectory : DynamicSpinCubeOffRayAdaptiveScalarTrajectory}
    {capacityProducer :
      DynamicSpinCubeOffRayAdaptiveRayCapacityProducer trajectory}
    (extension :
      DynamicSpinCubeOffRayAdaptiveTransitionProductExtension
        capacityProducer) :
    DynamicSpinCubeOffRayAdaptiveTransitionProductFamily :=
  extension.toLocalProducer.toDynamicFamily

/-- Compile to the existing completed carriers, transfers, and vacuum
sectors, conditionally on the one remaining extension. -/
def toCompletedFamily
    {trajectory : DynamicSpinCubeOffRayAdaptiveScalarTrajectory}
    {capacityProducer :
      DynamicSpinCubeOffRayAdaptiveRayCapacityProducer trajectory}
    (extension :
      DynamicSpinCubeOffRayAdaptiveTransitionProductExtension
        capacityProducer) :
    DynamicVacuumSectorCompletedFamily 0 :=
  extension.toLocalProducer.toCompletedFamily

/-- Preserve the existing exact normalized-strength law after compilation. -/
def toNormalizedStrengthLaw
    {trajectory : DynamicSpinCubeOffRayAdaptiveScalarTrajectory}
    {capacityProducer :
      DynamicSpinCubeOffRayAdaptiveRayCapacityProducer trajectory}
    (extension :
      DynamicSpinCubeOffRayAdaptiveTransitionProductExtension
        capacityProducer) :
    DynamicVacuumSectorNormalizedStrengthLaw extension.toCompletedFamily :=
  extension.toLocalProducer.toNormalizedStrengthLaw

end DynamicSpinCubeOffRayAdaptiveTransitionProductExtension

/-! ## 2. Concrete fixed-anchor scalar trajectory -/

theorem anchorCoupling_pos : (0 : Q') < anchorCoupling := by
  decide

theorem anchorCoupling_lt_one : anchorCoupling < (1 : Q') := by
  decide

/-- A geometric-spacing scalar trajectory whose nome stays at the exact
strong-coupling value where the cofinal ray theorem has been proved. -/
def anchorGeometricScalarTrajectory :
    DynamicSpinCubeOffRayAdaptiveScalarTrajectory where
  nome := fun _scale => anchorCoupling
  nome_pos := fun _scale => anchorCoupling_pos
  nome_lt_one := fun _scale => anchorCoupling_lt_one
  transferSpacing := canonicalAFGeometricPhysicalSpacing
  transferSpacingToZero := canonicalAFGeometricSpacingToZero

@[simp] theorem anchorGeometricScalarTrajectory_nome (scale : Nat) :
    anchorGeometricScalarTrajectory.nome scale = anchorCoupling := rfl

@[simp] theorem anchorGeometricScalarTrajectory_spacing (scale : Nat) :
    anchorGeometricScalarTrajectory.transferSpacing.spacing scale =
      canonicalAFGeometricSpacing scale := rfl

/-! ## 3. The existing uniform ray capacity lifted over every scale -/

/-- The proved fixed-nome cofinal capacity, reused without weakening at every
geometric scale.  This is legitimate precisely because the nome is literally
the fixed anchor at every scale. -/
def anchorGeometricRayCapacityProducer :
    DynamicSpinCubeOffRayAdaptiveRayCapacityProducer
      anchorGeometricScalarTrajectory where
  rayCapacity := fun _scale =>
    anchorCentralSpinCubeCofinalRayCapacity

@[simp] theorem anchorGeometricRayCapacityProducer_delta (scale : Nat) :
    (anchorGeometricRayCapacityProducer.rayCapacity scale).delta =
      anchorCentralSpinCubeCofinalRayCapacity.delta := rfl

theorem anchorGeometricRayCapacityProducer_delta_pos (scale : Nat) :
    (0 : Q') <
      (anchorGeometricRayCapacityProducer.rayCapacity scale).delta :=
  (anchorGeometricRayCapacityProducer.rayCapacity scale).delta_pos

/-! ## 4. One exact remaining field and its conditional compilation -/

/-- At the fixed-anchor/geometric trajectory, only the adaptive conditional
transition product remains.  No inhabitant is asserted. -/
abbrev AnchorGeometricAdaptiveTransitionProductExtension : Type 1 :=
  DynamicSpinCubeOffRayAdaptiveTransitionProductExtension
    anchorGeometricRayCapacityProducer

/-- Any inhabitant of the one-field extension produces the existing dynamic
family with the fixed anchor nome and the proved scale-independent capacity. -/
def anchorGeometricDynamicFamily
    (extension : AnchorGeometricAdaptiveTransitionProductExtension) :
    DynamicSpinCubeOffRayAdaptiveTransitionProductFamily :=
  extension.toDynamicFamily

/-- The same one-field extension produces the existing completed family. -/
def anchorGeometricCompletedFamily
    (extension : AnchorGeometricAdaptiveTransitionProductExtension) :
    DynamicVacuumSectorCompletedFamily 0 :=
  extension.toCompletedFamily

@[simp] theorem anchorGeometricDynamicFamily_nome
    (extension : AnchorGeometricAdaptiveTransitionProductExtension)
    (scale : Nat) :
    (anchorGeometricDynamicFamily extension).nome scale =
      anchorCoupling := rfl

@[simp] theorem anchorGeometricDynamicFamily_spacing
    (extension : AnchorGeometricAdaptiveTransitionProductExtension)
    (scale : Nat) :
    (anchorGeometricDynamicFamily extension).transferSpacing.spacing scale =
      canonicalAFGeometricSpacing scale := rfl

@[simp] theorem anchorGeometricDynamicFamily_rayCapacity_delta
    (extension : AnchorGeometricAdaptiveTransitionProductExtension)
    (scale : Nat) :
    ((anchorGeometricDynamicFamily extension).rayCapacity scale).delta =
      anchorCentralSpinCubeCofinalRayCapacity.delta := rfl

end YMGap.Continuum.BF4PhysicalAnchorDynamicRayCapacityCompiler

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalAnchorDynamicRayCapacityCompiler.DynamicSpinCubeOffRayAdaptiveTransitionProductExtension.toLocalProducer
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorDynamicRayCapacityCompiler.DynamicSpinCubeOffRayAdaptiveTransitionProductExtension.toCompletedFamily
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorDynamicRayCapacityCompiler.anchorCoupling_pos
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorDynamicRayCapacityCompiler.anchorCoupling_lt_one
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorDynamicRayCapacityCompiler.anchorGeometricScalarTrajectory
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorDynamicRayCapacityCompiler.anchorGeometricRayCapacityProducer
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorDynamicRayCapacityCompiler.anchorGeometricRayCapacityProducer_delta_pos
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorDynamicRayCapacityCompiler.anchorGeometricDynamicFamily
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorDynamicRayCapacityCompiler.anchorGeometricCompletedFamily
