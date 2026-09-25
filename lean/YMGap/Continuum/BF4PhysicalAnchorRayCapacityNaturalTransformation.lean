/-
# Presheaf transport of the inhabited anchor ray capacity

The anchor/geometric route already supplies a positive cofinal spin-ray
capacity at every scale.  The adaptive transition-product extension remains a
separate missing field.  This module exposes only the inhabited capacity
component as a natural transformation over the scale site.

The source fiber records a scale-indexed capacity producer together with the
explicit proof that this particular route is constant at the proved anchor
capacity.  The target fiber is the capacity visible at one scale.  The
constancy field is exactly what makes evaluation natural over the refinement
category; no transition product, completed family, physical-rate band, or
continuum object is manufactured here.
-/

import YMGap.Categorical.Core
import YMGap.Categorical.ScaleSheaf
import YMGap.Continuum.BF4PhysicalAnchorDynamicRayCapacityCompiler

namespace YMGap.Continuum.BF4PhysicalAnchorRayCapacityNaturalTransformation

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Categorical
open YMGap.Categorical.ScaleSheaf
open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalAnchorDynamicRayCapacityCompiler
open YMGap.Continuum.BF4CentralSpinCubeUniformRayCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## The honest scale-constant source certificate -/

/-- A producer whose ray-capacity component is explicitly pinned to the
inhabited strong-coupling anchor.  This is a Type-level constancy witness, not
an assertion that an arbitrary dynamic producer is constant. -/
structure AnchorConstantRayCapacityProducer : Type 1 where
  producer :
    DynamicSpinCubeOffRayAdaptiveRayCapacityProducer
      anchorGeometricScalarTrajectory
  capacity_eq : ∀ scale,
    producer.rayCapacity scale = anchorCentralSpinCubeCofinalRayCapacity

/-- One-scale capacity data, raised to the same universe as the source fiber. -/
structure AnchorRayCapacityAtScale : Type 1 where
  capacity : FixedNomeCofinalSpinCubeRayCapacity anchorCoupling_pos

/-- The positive scalar exposed by a capacity certificate. -/
structure AnchorRayCapacityDelta : Type 1 where
  value : Q'
  value_pos : (0 : Q') < value

/-! ## Constant presheaves and the evaluation arrow -/

def anchorConstantRayCapacityPresheaf :
    Presheaf ScaleCat (TypeCat.{1}) where
  obj := fun _ => AnchorConstantRayCapacityProducer
  map := fun _ => fun p => p
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

def anchorRayCapacityAtScalePresheaf :
    Presheaf ScaleCat (TypeCat.{1}) where
  obj := fun _ => AnchorRayCapacityAtScale
  map := fun _ => fun p => p
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

def anchorRayCapacityDeltaPresheaf :
    Presheaf ScaleCat (TypeCat.{1}) where
  obj := fun _ => AnchorRayCapacityDelta
  map := fun _ => fun p => p
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-- Evaluate the globally pinned producer at the current scale. -/
def anchorRayCapacityEvaluation : NatTrans
    anchorConstantRayCapacityPresheaf anchorRayCapacityAtScalePresheaf where
  app := fun scale pinned =>
    { capacity := pinned.producer.rayCapacity scale }
  naturality := by
    intro X Y f
    funext pinned
    cases pinned with
    | mk producer capacity_eq =>
        change AnchorRayCapacityAtScale.mk (producer.rayCapacity Y) =
          AnchorRayCapacityAtScale.mk (producer.rayCapacity X)
        rw [capacity_eq Y, capacity_eq X]

/-- Project the positive capacity to its scalar delta certificate. -/
def anchorRayCapacityToDelta : NatTrans
    anchorRayCapacityAtScalePresheaf anchorRayCapacityDeltaPresheaf where
  app := fun _ fiber =>
    { value := fiber.capacity.delta
      value_pos := fiber.capacity.delta_pos }
  naturality := fun _ => rfl

def anchorConstantRayCapacitySection :
    AnchorConstantRayCapacityProducer :=
  { producer := anchorGeometricRayCapacityProducer
    capacity_eq := fun _ => rfl }

theorem anchorRayCapacityEvaluation_section (scale : Nat) :
    (anchorRayCapacityEvaluation.app scale anchorConstantRayCapacitySection).capacity =
      anchorCentralSpinCubeCofinalRayCapacity := by
  exact anchorConstantRayCapacitySection.capacity_eq scale

theorem anchorRayCapacityEvaluation_delta_pos
    (scale : Nat) (p : anchorConstantRayCapacityPresheaf.obj scale) :
    (0 : Q') <
      (anchorRayCapacityToDelta.app scale
        (anchorRayCapacityEvaluation.app scale p)).value :=
  (anchorRayCapacityEvaluation.app scale p).capacity.delta_pos

end YMGap.Continuum.BF4PhysicalAnchorRayCapacityNaturalTransformation

#print axioms
  YMGap.Continuum.BF4PhysicalAnchorRayCapacityNaturalTransformation.AnchorConstantRayCapacityProducer
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorRayCapacityNaturalTransformation.AnchorRayCapacityAtScale
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorRayCapacityNaturalTransformation.AnchorRayCapacityDelta
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorRayCapacityNaturalTransformation.anchorConstantRayCapacityPresheaf
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorRayCapacityNaturalTransformation.anchorRayCapacityAtScalePresheaf
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorRayCapacityNaturalTransformation.anchorRayCapacityDeltaPresheaf
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorRayCapacityNaturalTransformation.anchorRayCapacityEvaluation
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorRayCapacityNaturalTransformation.anchorRayCapacityToDelta
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorRayCapacityNaturalTransformation.anchorConstantRayCapacitySection
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorRayCapacityNaturalTransformation.anchorRayCapacityEvaluation_section
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorRayCapacityNaturalTransformation.anchorRayCapacityEvaluation_delta_pos
