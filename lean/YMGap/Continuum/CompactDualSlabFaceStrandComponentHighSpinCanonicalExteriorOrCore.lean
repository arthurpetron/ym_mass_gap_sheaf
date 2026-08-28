/-
# Decide the canonical exterior-removal or finite-core branch

The canonical component family is already exhaustive, and every one of its
components already has an executable high-spin classification.  This module
assembles those pointwise classifications into one causal branch for the
complete accepted configuration.

Either the scan finds a canonical component whose reserve check succeeds, in
which case that component supplies an actual accepted adaptive-removal witness,
or every canonical component supplies a decoded core anchor.  In the latter
branch the emitted anchors are exactly the previously packed anchor list, so
the number of canonical components is bounded by

```text
(number of physical faces) * threshold.
```

This is an executable source classifier.  It does not estimate the total
weight of the finite-core branch or prove a posterior-variance fraction.

Constructive contract: structural recursion on the finite canonical component
list and the existing executable reserve classification only.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinAdaptiveFiberWeight
import YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalCoreFamily

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalExteriorOrCore

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveInverseFiber
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalCoreFamily
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCoreAnchor
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. One accepted exterior component is a fixed-target removal witness -/

/-- A canonical component over the complete boundary-link carrier directly
supplies the fixed-target removal witness consumed by the adaptive inverse-fiber
and weight estimates. -/
def SlabFaceStrandCanonicalComponent.adaptiveRemovalWitness
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (component : SlabFaceStrandCanonicalComponent
      (slabFusionWitnessAssignmentFaceStrandEdges
        K extent physical (boundaryCompleteSlabLinks extent)
          assignment hassignment)) :
    ComponentAdaptiveRemovalWitness K extent component.seed.root.faceId
      (SlabFusionWitnessFaceStrandSeed.peelFaces component.seed).length
      (SlabFusionWitnessFaceStrandSeed.lowerPhysical component.seed)
      (SlabFusionWitnessFaceStrandSeed.lowerAssignment component.seed)
      (physical, assignment) where
  sourceAssignment_mem := hassignment
  seed := component.seed
  rootFaceId_eq := rfl
  peelSize_eq := rfl
  lowerPhysical_eq := rfl
  lowerAssignment_eq := rfl

/-! ## 2. Structural scan of an arbitrary canonical subfamily -/

/-- One decoded core entry, retaining the equality showing that the executable
classification actually selected this anchor. -/
structure SlabCanonicalCoreEntry
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (threshold : Nat) : Type where
  component : SlabFaceStrandCanonicalComponent
    (slabFusionWitnessAssignmentFaceStrandEdges
      K extent physical links assignment hassignment)
  anchor : SlabComponentCoreAnchor component.seed threshold
  classification_eq : component.classification threshold = .core anchor

/-- The result of scanning a displayed canonical subfamily.  The exterior
branch gives the first peelable member found by the recursion.  The core branch
gives exactly one classified anchor entry per input component and identifies
the emitted anchor-copy list. -/
inductive SlabCanonicalItemsExteriorOrCore
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (threshold : Nat) :
    List (SlabFaceStrandCanonicalComponent
      (slabFusionWitnessAssignmentFaceStrandEdges
        K extent physical links assignment hassignment)) -> Type
  | exterior {items}
      (component : SlabFaceStrandCanonicalComponent
        (slabFusionWitnessAssignmentFaceStrandEdges
          K extent physical links assignment hassignment))
      (member : component ∈ items)
      (reserve_paid :
        SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck
          component.seed threshold = true) :
      SlabCanonicalItemsExteriorOrCore threshold items
  | core {items}
      (entries : List (SlabCanonicalCoreEntry threshold))
      (components_eq : entries.map (fun entry => entry.component) = items)
      (anchor_copies_eq :
        items.filterMap
            (SlabFaceStrandCanonicalComponent.coreAnchor? threshold) =
          entries.map (fun entry => entry.anchor.copy)) :
      SlabCanonicalItemsExteriorOrCore threshold items

/-- Structurally scan a canonical component list until an exterior component
is found, retaining a complete ordered core certificate if none exists. -/
def classifySlabCanonicalItemsExteriorOrCore
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (threshold : Nat) :
    (items : List (SlabFaceStrandCanonicalComponent
      (slabFusionWitnessAssignmentFaceStrandEdges
        K extent physical links assignment hassignment))) ->
      SlabCanonicalItemsExteriorOrCore threshold items
  | [] => .core [] rfl rfl
  | component :: tail =>
      match hclass : component.classification threshold with
      | .exterior reserve_paid =>
          .exterior component List.mem_cons_self reserve_paid
      | .core anchor =>
          match classifySlabCanonicalItemsExteriorOrCore threshold tail with
          | .exterior exteriorComponent member reserve_paid =>
              .exterior exteriorComponent
                (List.mem_cons_of_mem component member) reserve_paid
          | .core entries components_eq anchor_copies_eq =>
              .core
                ({ component := component
                   anchor := anchor
                   classification_eq := hclass } :: entries)
                (by simp only [List.map_cons, components_eq])
                (by
                  simp only [List.filterMap_cons, List.map_cons]
                  unfold SlabFaceStrandCanonicalComponent.coreAnchor?
                  rw [hclass]
                  exact congrArg (List.cons anchor.copy) anchor_copies_eq)

/-! ## 3. The complete accepted-configuration branch -/

/-- The complete source classifier either supplies an exterior canonical
component or certifies that every canonical component is represented in the
finite-core anchor list, with its resulting finite count bound. -/
inductive SlabCanonicalExteriorOrFiniteCore
    (K extent : Nat) (physical : SlabLabelling)
    (links : List SlabLink) (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links)
    (threshold : Nat) : Type
  | exterior
      (component : SlabFaceStrandCanonicalComponent
        (slabFusionWitnessAssignmentFaceStrandEdges
          K extent physical links assignment hassignment))
      (reserve_paid :
        SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck
          component.seed threshold = true)
  | finiteCore
      (entries : List (SlabCanonicalCoreEntry threshold))
      (components_eq :
        entries.map (fun entry => entry.component) =
          (slabFaceStrandCanonicalComponents
            (slabFusionWitnessAssignmentFaceStrandEdges
              K extent physical links assignment hassignment)).attach)
      (anchor_copies_eq :
        slabCanonicalCoreAnchorCopies K extent physical links assignment
            hassignment threshold =
          entries.map (fun entry => entry.anchor.copy))
      (component_count_le :
        (slabFaceStrandCanonicalComponents
          (slabFusionWitnessAssignmentFaceStrandEdges
            K extent physical links assignment hassignment)).length <=
          (slabPhysicalFaceEdges extent).length * threshold)

/-- Evaluate the complete canonical family.  In the all-core branch, exact
component coverage converts the pre-existing anchor-copy packing theorem into
the desired bound on the number of components themselves. -/
def slabCanonicalExteriorOrFiniteCore
    (K extent : Nat) (physical : SlabLabelling)
    (links : List SlabLink) (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links)
    (threshold : Nat) :
    SlabCanonicalExteriorOrFiniteCore K extent physical links assignment
      hassignment threshold := by
  let edges := slabFusionWitnessAssignmentFaceStrandEdges
    K extent physical links assignment hassignment
  let components := slabFaceStrandCanonicalComponents edges
  cases classifySlabCanonicalItemsExteriorOrCore
      threshold components.attach with
  | exterior component member reserve_paid =>
      exact .exterior component reserve_paid
  | core entries components_eq anchor_copies_eq =>
      apply SlabCanonicalExteriorOrFiniteCore.finiteCore
        entries components_eq
      · unfold slabCanonicalCoreAnchorCopies
        exact anchor_copies_eq
      · have hcomponentsLength : entries.length = components.length := by
          have hlength := congrArg List.length components_eq
          simpa only [List.length_map, List.length_attach] using hlength
        have hanchorsLength :
            (slabCanonicalCoreAnchorCopies K extent physical links assignment
              hassignment threshold).length = entries.length := by
          have hlength := congrArg List.length anchor_copies_eq
          simpa only [List.length_map] using hlength
        calc
          components.length = entries.length := hcomponentsLength.symm
          _ = (slabCanonicalCoreAnchorCopies K extent physical links assignment
                hassignment threshold).length := hanchorsLength.symm
          _ <= (slabPhysicalFaceEdges extent).length * threshold :=
            slabCanonicalCoreAnchorCopies_length_le_faces_mul_threshold
              K extent physical links assignment hassignment threshold

#print axioms SlabFaceStrandCanonicalComponent.adaptiveRemovalWitness
#print axioms SlabCanonicalCoreEntry
#print axioms SlabCanonicalItemsExteriorOrCore
#print axioms classifySlabCanonicalItemsExteriorOrCore
#print axioms SlabCanonicalExteriorOrFiniteCore
#print axioms slabCanonicalExteriorOrFiniteCore

end YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCanonicalExteriorOrCore
