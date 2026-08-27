/-
# Exact physical-mass descent under one component peel

The existing component removal lowers each physical face by the number of
selected strand copies and serializes precisely those decrements in
`peelFaces`.  This module records the corresponding conservation law for
total twice-spin mass:

  mass(lowerPhysical) + peelFaces.length = mass(physical).

Since every rooted peel is nonempty, total physical mass decreases strictly.
This is the well-founded quantity needed to iterate accepted component
removals through a paired-support component.

Constructive contract: finite natural-number sums and exact subtraction
only; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight
import YMGap.Continuum.FiniteSimpleWalk

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentMassDrop

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentGlobalAuxiliaryL1
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. Total physical twice-spin mass -/

def slabPhysicalLabellingMass
    (extent : Nat) (physical : SlabLabelling) : Nat :=
  listNatWeight physical (slabPhysicalFaceEdges extent)

private theorem natListSum_map_eq_listNatWeight
    {A : Type} (weight : A → Nat) :
    ∀ items : List A,
      natListSum (items.map weight) = listNatWeight weight items
  | [] => rfl
  | head :: tail => by
      simp only [List.map_cons, natListSum, listNatWeight]
      rw [natListSum_map_eq_listNatWeight weight tail]

private theorem listNatWeight_sub_add_drop
    {A : Type} (value drop : A → Nat) :
    ∀ items : List A,
      (∀ item, item ∈ items → drop item ≤ value item) →
        listNatWeight (fun item => value item - drop item) items +
            listNatWeight drop items =
          listNatWeight value items
  | [], _ => rfl
  | head :: tail, hle => by
      have hhead := hle head List.mem_cons_self
      have htail := listNatWeight_sub_add_drop value drop tail
        (fun item hitem => hle item (List.mem_cons_of_mem head hitem))
      simp only [listNatWeight]
      omega

/-! ## 2. Exact descent for one accepted rooted component -/

/-- The serialized component peel is exactly the physical mass removed by
the accepted lower state. -/
theorem SlabFusionWitnessFaceStrandSeed.lowerPhysical_mass_add_peel_length
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    slabPhysicalLabellingMass extent
          (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed) +
        (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length =
      slabPhysicalLabellingMass extent physical := by
  let drop : Nat → Nat :=
    slabFaceStrandSelectionCount seed.selected
  have hsum := listNatWeight_sub_add_drop physical drop
    (slabPhysicalFaceEdges extent)
    (fun faceId _ => slabFaceStrandSelectionCount_le seed.selected faceId)
  have hpeel :=
    SlabFusionWitnessFaceStrandSeed.peelFaces_length_eq_physicalDrop_l1
      seed
  rw [natListSum_map_eq_listNatWeight drop
    (slabPhysicalFaceEdges extent)] at hpeel
  unfold slabPhysicalLabellingMass
  unfold SlabFusionWitnessFaceStrandSeed.lowerPhysical
    lowerSlabPhysicalByFaceStrandSelection lowerEdgeLabellingBy
  change
    listNatWeight (fun faceId => physical faceId - drop faceId)
          (slabPhysicalFaceEdges extent) +
        (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length =
      listNatWeight physical (slabPhysicalFaceEdges extent)
  rw [hpeel]
  exact hsum

/-- Every rooted accepted component peel strictly decreases total physical
twice-spin mass. -/
theorem SlabFusionWitnessFaceStrandSeed.lowerPhysical_mass_lt
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    slabPhysicalLabellingMass extent
        (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed) <
      slabPhysicalLabellingMass extent physical := by
  have hmass :=
    SlabFusionWitnessFaceStrandSeed.lowerPhysical_mass_add_peel_length seed
  have hpeel :=
    SlabFusionWitnessFaceStrandSeed.peelFaces_length_pos seed
  omega

end YMGap.Continuum.CompactDualSlabFaceStrandComponentMassDrop

#print axioms YMGap.Continuum.CompactDualSlabFaceStrandComponentMassDrop.slabPhysicalLabellingMass
#print axioms YMGap.Continuum.CompactDualSlabFaceStrandComponentMassDrop.SlabFusionWitnessFaceStrandSeed.lowerPhysical_mass_add_peel_length
#print axioms YMGap.Continuum.CompactDualSlabFaceStrandComponentMassDrop.SlabFusionWitnessFaceStrandSeed.lowerPhysical_mass_lt
