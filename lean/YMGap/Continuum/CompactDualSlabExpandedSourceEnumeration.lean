/-
# The literal expanded finite source enumeration

The component-removal estimate is stated for pairs consisting of a physical
face labelling and one accepted complete fine-intertwiner assignment.  This
module constructs exactly that finite carrier from the production slab data.
It proves that neither the physical Cartesian enumeration nor any local or
global intertwiner fiber introduces duplicates, and that summing the literal
expanded-fiber weight over the carrier recovers the genuine corrected-slab
physical partition.

For a fixed observable face, filtering to sources with positive spin at that
face preserves duplicate-freeness.  Every member of this rooted subcarrier
constructs the slot-zero observable component from
`CompactDualSlabObservableRootSeed`.

Constructive contract: structural finite-list arguments and exact rational
Fubini only.  No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservableRootSeed
import YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight
import YMGap.Continuum.Z4BoundedEdgeLabellingNodup

namespace YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabObservableRootSeed
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4BoundedEdgeLabellingNodup
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Duplicate-free local and global intertwiner fibers -/

private theorem nodup_flatMap_of_disjoint_blocks
    {A B : Type} (block : A → List B) :
    ∀ source : List A, source.Nodup →
      (∀ item, item ∈ source → (block item).Nodup) →
      (∀ left, left ∈ source → ∀ right, right ∈ source →
        left ≠ right → ∀ value, value ∈ block left →
          value ∉ block right) →
      (source.flatMap block).Nodup
  | [], _, _, _ => List.nodup_nil
  | head :: tail, hsource, hblocks, hdisjoint => by
      have hparts := List.nodup_cons.mp hsource
      rw [List.flatMap_cons]
      apply List.nodup_append.mpr
      refine ⟨hblocks head List.mem_cons_self,
        nodup_flatMap_of_disjoint_blocks block tail hparts.2
          (fun item hitem =>
            hblocks item (List.mem_cons_of_mem head hitem))
          (fun left hleft right hright hne =>
            hdisjoint left (List.mem_cons_of_mem head hleft)
              right (List.mem_cons_of_mem head hright) hne), ?_⟩
      intro value hhead other htail heq
      have hvalueTail : value ∈ tail.flatMap block := by
        rw [heq]
        exact htail
      obtain ⟨item, hitem, hvalueItem⟩ :=
        List.mem_flatMap.mp hvalueTail
      have hne : head ≠ item := by
        intro hsame
        subst item
        exact hparts.1 hitem
      exact (hdisjoint head List.mem_cons_self item
        (List.mem_cons_of_mem head hitem) hne value hhead) hvalueItem

private theorem range_nodup_local :
    ∀ count : Nat, (List.range count).Nodup
  | 0 => List.nodup_nil
  | count + 1 => by
      rw [List.range_succ]
      exact List.nodup_append.mpr
        ⟨range_nodup_local count,
          List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
          fun item hitem member hmember => by
            have hmemberEq : member = count := List.mem_singleton.mp hmember
            subst member
            exact Nat.ne_of_lt (List.mem_range.mp hitem)⟩

/-- Every accepted auxiliary list at one corrected-slab link is
duplicate-free. -/
theorem slabLinkFusionWitnesses_nodup
    (cutoff extent : Nat) (physical : SlabLabelling) (link : SlabLink) :
    (slabLinkFusionWitnesses cutoff extent physical link).Nodup := by
  unfold slabLinkFusionWitnesses
  exact (boundedEdgeLabellings_nodup _ _
    (canonicalUsedAuxiliaryCoordinates_nodup
      (slabIncidentPlaqIds_length_le_six extent link))).filter _

/-- Recursive Cartesian assembly of accepted link witnesses introduces no
duplicate global assignment. -/
theorem slabFusionWitnessAssignmentsOn_nodup
    (cutoff extent : Nat) (physical : SlabLabelling) :
    ∀ links : List SlabLink,
      (slabFusionWitnessAssignmentsOn
        cutoff extent physical links).Nodup
  | [] => List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  | link :: rest => by
      unfold slabFusionWitnessAssignmentsOn
      apply nodup_flatMap_of_disjoint_blocks
      · exact slabLinkFusionWitnesses_nodup cutoff extent physical link
      · intro auxiliary _
        apply YMGap.Continuum.CayleyPruferInjection.nodup_map_of_injOn
        · exact slabFusionWitnessAssignmentsOn_nodup
            cutoff extent physical rest
        · intro left _ right _ heq
          injection heq
      · intro left _ right _ hne value hleft hright
        obtain ⟨leftTail, _, hleftEq⟩ := List.mem_map.mp hleft
        obtain ⟨rightTail, _, hrightEq⟩ := List.mem_map.mp hright
        have heq : (link, left) :: leftTail =
            (link, right) :: rightTail := by
          exact hleftEq.trans hrightEq.symm
        have hhead : (link, left) = (link, right) := by
          injection heq
        exact hne (congrArg Prod.snd hhead)

/-- The production complete fine-intertwiner fiber is duplicate-free. -/
theorem slabFineFusionWitnesses_nodup
    (D : SlabPhysicalData) (physical : SlabLabelling) :
    (slabFineFusionWitnesses D physical).Nodup := by
  unfold slabFineFusionWitnesses
  exact slabFusionWitnessAssignmentsOn_nodup
    D.cutoff D.extent physical (boundaryCompleteSlabLinks D.extent)

/-- The physical Cartesian carrier of a corrected slab is duplicate-free. -/
theorem slabPhysicalLabellings_nodup (D : SlabPhysicalData) :
    D.physicalLabellings.Nodup := by
  unfold SlabPhysicalData.physicalLabellings SlabPhysicalData.faceEdges
    slabPhysicalFaceEdges
  exact boundedEdgeLabellings_nodup D.cutoff _
    (range_nodup_local _)

/-! ## 2. The exact expanded source carrier and its weight -/

/-- Every physical slab labelling paired with every literal accepted global
fine-intertwiner assignment above it. -/
def slabExpandedFineSourceBlock
    (D : SlabPhysicalData) (physical : SlabLabelling) :
    List (SlabLabelling × SlabFusionWitnessAssignment) :=
  (slabFineFusionWitnesses D physical).map fun assignment =>
    (physical, assignment)

def slabExpandedFineSources (D : SlabPhysicalData) :
    List (SlabLabelling × SlabFusionWitnessAssignment) :=
  D.physicalLabellings.flatMap (slabExpandedFineSourceBlock D)

/-- The literal unnormalized weight carried by one expanded source pair. -/
def slabExpandedFineSourceWeight
    (D : SlabPhysicalData)
    (source : SlabLabelling × SlabFusionWitnessAssignment) : Q' :=
  retainedFineIntertwinerPhysicalFiberWeight D source.1 source.2

/-- Membership exposes exactly the physical and conditional-assignment
membership data. -/
theorem mem_slabExpandedFineSources_iff
    {D : SlabPhysicalData}
    {source : SlabLabelling × SlabFusionWitnessAssignment} :
    source ∈ slabExpandedFineSources D ↔
      source.1 ∈ D.physicalLabellings ∧
      source.2 ∈ slabFineFusionWitnesses D source.1 := by
  constructor
  · intro hsource
    obtain ⟨physical, hphysical, hblock⟩ :=
      List.mem_flatMap.mp hsource
    obtain ⟨assignment, hassignment, heq⟩ :=
      List.mem_map.mp hblock
    have hphysicalEq : physical = source.1 := by
      rw [← heq]
    have hassignmentEq : assignment = source.2 := by
      rw [← heq]
    exact ⟨hphysicalEq ▸ hphysical,
      hphysicalEq ▸ hassignmentEq ▸ hassignment⟩
  · intro hsource
    apply List.mem_flatMap.mpr
    refine ⟨source.1, hsource.1, ?_⟩
    exact List.mem_map.mpr ⟨source.2, hsource.2, rfl⟩

/-- The full expanded source enumeration is duplicate-free. -/
theorem slabExpandedFineSources_nodup (D : SlabPhysicalData) :
    (slabExpandedFineSources D).Nodup := by
  unfold slabExpandedFineSources
  apply nodup_flatMap_of_disjoint_blocks
  · exact slabPhysicalLabellings_nodup D
  · intro physical _
    apply YMGap.Continuum.CayleyPruferInjection.nodup_map_of_injOn
    · exact slabFineFusionWitnesses_nodup D physical
    · intro left _ right _ heq
      exact congrArg Prod.snd heq
  · intro left _ right _ hne value hleft hright
    obtain ⟨leftAssignment, _, hleftEq⟩ := List.mem_map.mp hleft
    obtain ⟨rightAssignment, _, hrightEq⟩ := List.mem_map.mp hright
    have hpairs : (left, leftAssignment) =
        (right, rightAssignment) := by
      exact hleftEq.trans hrightEq.symm
    exact hne (congrArg Prod.fst hpairs)

/-- On one physical block, mapping assignments into source pairs does not
change the literal fiber-weight sum. -/
theorem slabExpandedFineSourceBlock_weight
    (D : SlabPhysicalData) (physical : SlabLabelling) :
    listQSum
        (slabExpandedFineSourceWeight D)
        (slabExpandedFineSourceBlock D physical) ≈
      listQSum
        (retainedFineIntertwinerPhysicalFiberWeight D physical)
        (slabFineFusionWitnesses D physical) := by
  unfold slabExpandedFineSourceBlock
  rw [listQSum_map]
  apply listQSum_congr
  intro assignment
  exact Q'.eqv_refl _

/-- Summing the expanded source weights gives exactly the genuine physical
corrected-slab partition. -/
theorem slabExpandedFineSources_weight_total (D : SlabPhysicalData) :
    listQSum (slabExpandedFineSourceWeight D)
        (slabExpandedFineSources D) ≈
      D.physicalPartition := by
  refine Q'.eqv_trans _
    (listQSum
      (fun physical =>
        listQSum
          (slabExpandedFineSourceWeight D)
          (slabExpandedFineSourceBlock D physical))
      D.physicalLabellings) _ ?_ ?_
  · unfold slabExpandedFineSources
    exact listQSum_flatMap
      (slabExpandedFineSourceWeight D)
      (slabExpandedFineSourceBlock D) D.physicalLabellings
  refine Q'.eqv_trans _
    (listQSum
      (fun physical =>
        listQSum
          (retainedFineIntertwinerPhysicalFiberWeight D physical)
          (slabFineFusionWitnesses D physical))
      D.physicalLabellings) _ ?_ ?_
  · apply listQSum_congr
    intro physical
    exact slabExpandedFineSourceBlock_weight D physical
  · unfold SlabPhysicalData.physicalPartition
      SlabPhysicalData.physicalLabellings SlabPhysicalData.faceEdges
      slabParametricKPhysicalPartition
    apply listQSum_congr
    intro physical
    exact retainedFineIntertwinerPhysicalFiberWeight_total D physical

/-! ## 3. The observable-rooted subcarrier -/

/-- Expanded sources whose fixed observable face carries at least one physical
strand. -/
def slabObservablePositiveExpandedSources
    (D : SlabPhysicalData) (faceId : Nat) :
    List (SlabLabelling × SlabFusionWitnessAssignment) :=
  (slabExpandedFineSources D).filter fun source =>
    decide (0 < source.1 faceId)

theorem mem_slabObservablePositiveExpandedSources_iff
    {D : SlabPhysicalData} {faceId : Nat}
    {source : SlabLabelling × SlabFusionWitnessAssignment} :
    source ∈ slabObservablePositiveExpandedSources D faceId ↔
      source ∈ slabExpandedFineSources D ∧ 0 < source.1 faceId := by
  simp [slabObservablePositiveExpandedSources]

/-- Filtering to a fixed positive observable face preserves
duplicate-freeness. -/
theorem slabObservablePositiveExpandedSources_nodup
    (D : SlabPhysicalData) (faceId : Nat) :
    (slabObservablePositiveExpandedSources D faceId).Nodup :=
  (slabExpandedFineSources_nodup D).filter _

/-- Every member of the literal positive-face subcarrier has the canonical
slot-zero observable-rooted component. -/
def slabObservablePositiveExpandedSourceSeed
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabLabelling × SlabFusionWitnessAssignment)
    (hsource : source ∈
      slabObservablePositiveExpandedSources D faceId) :
    SlabFusionWitnessFaceStrandSeed D.cutoff D.extent source.1
      (boundaryCompleteSlabLinks D.extent) source.2
      ((mem_slabExpandedFineSources_iff.mp
        (mem_slabObservablePositiveExpandedSources_iff.mp hsource).1).2) :=
  slabObservableRootSeed D.cutoff D.extent faceId hface source.1
    (mem_slabObservablePositiveExpandedSources_iff.mp hsource).2 source.2
    ((mem_slabExpandedFineSources_iff.mp
      (mem_slabObservablePositiveExpandedSources_iff.mp hsource).1).2)

#print axioms slabLinkFusionWitnesses_nodup
#print axioms slabFusionWitnessAssignmentsOn_nodup
#print axioms slabFineFusionWitnesses_nodup
#print axioms slabPhysicalLabellings_nodup
#print axioms slabExpandedFineSourceBlock
#print axioms slabExpandedFineSources
#print axioms slabExpandedFineSourceWeight
#print axioms mem_slabExpandedFineSources_iff
#print axioms slabExpandedFineSources_nodup
#print axioms slabExpandedFineSourceBlock_weight
#print axioms slabExpandedFineSources_weight_total
#print axioms slabObservablePositiveExpandedSources
#print axioms mem_slabObservablePositiveExpandedSources_iff
#print axioms slabObservablePositiveExpandedSources_nodup
#print axioms slabObservablePositiveExpandedSourceSeed

end YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
