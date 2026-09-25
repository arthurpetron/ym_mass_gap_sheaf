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
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDecision

namespace YMGap.Continuum.BF4PhysicalAnchorRayCapacityNaturalTransformation

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Categorical
open YMGap.Categorical.ScaleSheaf
open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalAnchorDynamicRayCapacityCompiler
open YMGap.Continuum.BF4CentralSpinCubeUniformRayCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDecision
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeFiniteLinearFullSectorCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor
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

/-! ## The first finite transition-product consumer -/

abbrev AnchorFiniteMarginAtZero : Type 1 :=
  CentralLowerExcitedSpinCubeOffRayResidualRoutedFiniteCapacityMarginAt
    (w := anchorCoupling) (hw := by decide) 0
    (anchorCentralSpinCubeFiniteRayCapacityAt 0)
    (canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      anchorCoupling (by decide) 0)

abbrev AnchorFiniteProductAtZero : Type 1 :=
  CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductAt
    (w := anchorCoupling) (hw := by decide) 0
    (anchorCentralSpinCubeFiniteRayCapacityAt 0)
    (canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      anchorCoupling (by decide) 0)

/-- The finite cutoff-zero transition-product certificate attached to the
anchor capacity.  Its existence is not promoted to a cofinal success family. -/
structure AnchorFiniteTransitionAtZero : Type 1 where
  capacity : FixedNomeCofinalSpinCubeRayCapacity anchorCoupling_pos
  capacity_eq : capacity = anchorCentralSpinCubeCofinalRayCapacity
  margin : AnchorFiniteMarginAtZero
  product : AnchorFiniteProductAtZero

def anchorFiniteTransitionAtZero : AnchorFiniteTransitionAtZero where
  capacity := anchorCentralSpinCubeCofinalRayCapacity
  capacity_eq := rfl
  margin := anchorCanonicalFiniteCapacityMarginAt_zero
  product := anchorCanonicalRoutedConditionalTransitionProductAt_zero

def anchorFiniteTransitionAtZeroPresheaf :
    Presheaf ScaleCat (TypeCat.{1}) where
  obj := fun _ => AnchorFiniteTransitionAtZero
  map := fun _ => fun p => p
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-- Every explicitly constant anchor-capacity section carries the checked
cutoff-zero margin and routed transition-product witness. -/
def anchorRayCapacityToFiniteTransitionAtZero : NatTrans
    anchorConstantRayCapacityPresheaf anchorFiniteTransitionAtZeroPresheaf where
  app := fun _ pinned =>
    { capacity := pinned.producer.rayCapacity 0
      capacity_eq := pinned.capacity_eq 0
      margin := anchorCanonicalFiniteCapacityMarginAt_zero
      product := anchorCanonicalRoutedConditionalTransitionProductAt_zero }
  naturality := fun _ => rfl

theorem anchorRayCapacityToFiniteTransitionAtZero_section (scale : Nat) :
    (anchorRayCapacityToFiniteTransitionAtZero.app scale
      anchorConstantRayCapacitySection).margin =
      anchorCanonicalFiniteCapacityMarginAt_zero := rfl

/-! ## The cutoff-indexed finite-linear transition family -/

/-- A finite-linear transition witness at one scale.  Its ray capacity is the
cutoff-dependent restricted capacity, so this object is not the cofinal
shared-floor witness above. -/
structure AnchorFiniteLinearTransition : Type 1 where
  producer : AnchorConstantRayCapacityProducer
  cutoff : Nat
  capacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt
    anchorCoupling_pos cutoff
  product : CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductAt
    (w := anchorCoupling) (hw := anchorCoupling_pos) cutoff
    (centralLowerExcitedSpinCubeFiniteLinearRestrictedRayCapacity capacity)
    (canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      anchorCoupling (Q'.le_of_lt anchorCoupling_pos) cutoff)

def anchorFiniteLinearTransitionAtScale (scale : Nat) :
    AnchorFiniteLinearTransition where
  producer := anchorConstantRayCapacitySection
  cutoff := scale
  capacity := centralLowerExcitedSpinCubeFiniteRayCapacityAt
    anchorCoupling_pos scale
  product := centralLowerExcitedSpinCubeFiniteLinearRoutedConditionalTransitionProductAt
    (w := anchorCoupling) (hw := anchorCoupling_pos) (K := scale)
    (centralLowerExcitedSpinCubeFiniteRayCapacityAt anchorCoupling_pos scale)

/-! The cutoff varies inside a family object, not in the presheaf maps.  This
is the constructive shape required by naturality: a constant presheaf may
transport a whole scale-indexed family by identity, while the family itself
records the finite product at each cutoff. -/

structure AnchorFiniteLinearTransitionFamily : Type 1 where
  producer : AnchorConstantRayCapacityProducer
  atScale : ∀ scale, AnchorFiniteLinearTransition
  at_producer : ∀ scale, (atScale scale).producer = producer
  at_cutoff : ∀ scale, (atScale scale).cutoff = scale

def anchorFiniteLinearTransitionFamilyOfProducer
    (p : AnchorConstantRayCapacityProducer) :
    AnchorFiniteLinearTransitionFamily where
  producer := p
  atScale := fun scale =>
    { producer := p
      cutoff := scale
      capacity := centralLowerExcitedSpinCubeFiniteRayCapacityAt
        anchorCoupling_pos scale
      product := centralLowerExcitedSpinCubeFiniteLinearRoutedConditionalTransitionProductAt
        (w := anchorCoupling) (hw := anchorCoupling_pos) (K := scale)
        (centralLowerExcitedSpinCubeFiniteRayCapacityAt anchorCoupling_pos scale) }
  at_producer := fun _ => rfl
  at_cutoff := fun _ => rfl

def anchorFiniteLinearTransitionFamilyPresheaf :
    Presheaf ScaleCat (TypeCat.{1}) where
  obj := fun _ => AnchorFiniteLinearTransitionFamily
  map := fun _ => fun p => p
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-- The scale-indexed finite-linear product retains the anchor producer while
exposing the exact cutoff-dependent restricted ray capacity. -/
def anchorRayCapacityToFiniteLinearTransitionFamily : NatTrans
    anchorConstantRayCapacityPresheaf
      anchorFiniteLinearTransitionFamilyPresheaf where
  app := fun _ pinned => anchorFiniteLinearTransitionFamilyOfProducer pinned
  naturality := fun _ => rfl

theorem anchorRayCapacityToFiniteLinearTransitionFamily_producer
    (scale : Nat) (p : anchorConstantRayCapacityPresheaf.obj scale) :
    (anchorRayCapacityToFiniteLinearTransitionFamily.app scale p).producer = p := by
  rfl

theorem anchorFiniteLinearTransitionAtScale_capacity_pos (scale : Nat) :
    (0 : Q') <
      (anchorFiniteLinearTransitionAtScale scale).capacity.delta :=
  (anchorFiniteLinearTransitionAtScale scale).capacity.delta_pos

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
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorRayCapacityNaturalTransformation.AnchorFiniteMarginAtZero
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorRayCapacityNaturalTransformation.AnchorFiniteProductAtZero
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorRayCapacityNaturalTransformation.AnchorFiniteTransitionAtZero
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorRayCapacityNaturalTransformation.anchorFiniteTransitionAtZero
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorRayCapacityNaturalTransformation.anchorFiniteTransitionAtZeroPresheaf
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorRayCapacityNaturalTransformation.anchorRayCapacityToFiniteTransitionAtZero
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorRayCapacityNaturalTransformation.anchorRayCapacityToFiniteTransitionAtZero_section
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorRayCapacityNaturalTransformation.AnchorFiniteLinearTransition
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorRayCapacityNaturalTransformation.AnchorFiniteLinearTransitionFamily
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorRayCapacityNaturalTransformation.anchorFiniteLinearTransitionFamilyOfProducer
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorRayCapacityNaturalTransformation.anchorFiniteLinearTransitionFamilyPresheaf
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorRayCapacityNaturalTransformation.anchorRayCapacityToFiniteLinearTransitionFamily
#print axioms
  YMGap.Continuum.BF4PhysicalAnchorRayCapacityNaturalTransformation.anchorFiniteLinearTransitionAtScale_capacity_pos
