/-
# Decidable finite-support keys for expanded slab targets

The literal expanded source carrier contains function-valued physical and
auxiliary labellings, so equality of source pairs is not directly decidable.
Component-removal fibers nevertheless have finite support: physical targets
vanish off the corrected-slab face list, and every local auxiliary target
vanishes off the canonical coordinates of its displayed link.

This module records those finite values as an explicit decidable key.  The
production support theorems and exact global-assignment reconstruction prove
that the key is injective on the actual expanded carrier.  The resulting key
list is duplicate-free, and every target produced by an accepted rooted
component peel belongs to it.

Constructive contract: finite list maps, explicit support equalities, and the
already proved assignment reconstruction theorem only.  No `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, noncomputable declaration, or
enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
import YMGap.Continuum.CompactDualSlabFaceStrandComponentReconstruction

namespace YMGap.Continuum.CompactDualSlabExpandedTargetKey

set_option autoImplicit false

open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentReconstruction
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

/-! ## 1. Finite words determine supported labellings -/

private theorem map_functions_eq_on_mem
    {A B : Type} (items : List A) (left right : A -> B)
    (hmap : items.map left = items.map right) :
    forall item, item ∈ items -> left item = right item := by
  induction items with
  | nil =>
      intro item hitem
      exact False.elim (List.not_mem_nil hitem)
  | cons head tail ih =>
      simp only [List.map_cons] at hmap
      have hhead : left head = right head := by
        injection hmap
      have htail : tail.map left = tail.map right := by
        injection hmap
      intro item hitem
      rcases List.mem_cons.mp hitem with heq | htailMem
      · subst item
        exact hhead
      · exact ih htail item htailMem

/-- Read an edge labelling on one displayed finite support. -/
def finiteEdgeLabellingWord
    (edges : List Nat) (labelling : EdgeLabelling) : List Nat :=
  edges.map labelling

/-- Equal finite words determine equal labellings when both labellings vanish
off the displayed support. -/
theorem edgeLabelling_eq_of_word_eq_of_supported
    (edges : List Nat) (left right : EdgeLabelling)
    (hleft : forall edge, edge ∉ edges -> left edge = 0)
    (hright : forall edge, edge ∉ edges -> right edge = 0)
    (hword : finiteEdgeLabellingWord edges left =
      finiteEdgeLabellingWord edges right) :
    left = right := by
  funext edge
  by_cases hedge : edge ∈ edges
  · exact map_functions_eq_on_mem edges left right hword edge hedge
  · rw [hleft edge hedge, hright edge hedge]

/-! ## 2. Ordered words determine a complete fusion assignment -/

/-- At every displayed link, record the target auxiliary labelling on exactly
the canonical coordinates read by the local resolver. -/
def slabFusionWitnessAssignmentWords
    (extent : Nat) (assignment : SlabFusionWitnessAssignment) :
    List (List Nat) :=
  (boundaryCompleteSlabLinks extent).map fun link =>
    finiteEdgeLabellingWord
      (canonicalUsedAuxiliaryCoordinates
        (slabIncidentPlaqIds extent link).length)
      (slabFusionWitnessAssignmentAt link assignment)

/-- On the production Cartesian assignment carrier, equality of all ordered
link-local words implies literal equality of the complete assignments. -/
theorem slabFusionWitnessAssignment_eq_of_words_eq
    (K extent : Nat)
    (leftPhysical rightPhysical : SlabLabelling)
    (left right : SlabFusionWitnessAssignment)
    (hleft : left ∈ slabFusionWitnessAssignmentsOn K extent leftPhysical
      (boundaryCompleteSlabLinks extent))
    (hright : right ∈ slabFusionWitnessAssignmentsOn K extent rightPhysical
      (boundaryCompleteSlabLinks extent))
    (hwords : slabFusionWitnessAssignmentWords extent left =
      slabFusionWitnessAssignmentWords extent right) :
    left = right := by
  let links := boundaryCompleteSlabLinks extent
  have hlookup : forall link, link ∈ links ->
      slabFusionWitnessAssignmentAt link left =
        slabFusionWitnessAssignmentAt link right := by
    intro link hlink
    let edges := canonicalUsedAuxiliaryCoordinates
      (slabIncidentPlaqIds extent link).length
    have hword : finiteEdgeLabellingWord edges
        (slabFusionWitnessAssignmentAt link left) =
      finiteEdgeLabellingWord edges
        (slabFusionWitnessAssignmentAt link right) := by
      exact map_functions_eq_on_mem links
        (fun candidate =>
          finiteEdgeLabellingWord
            (canonicalUsedAuxiliaryCoordinates
              (slabIncidentPlaqIds extent candidate).length)
            (slabFusionWitnessAssignmentAt candidate left))
        (fun candidate =>
          finiteEdgeLabellingWord
            (canonicalUsedAuxiliaryCoordinates
              (slabIncidentPlaqIds extent candidate).length)
            (slabFusionWitnessAssignmentAt candidate right))
        hwords link hlink
    have hleftLocal := slabFusionWitnessAssignmentAt_mem_local
      K extent leftPhysical links left hleft link hlink
    have hrightLocal := slabFusionWitnessAssignmentAt_mem_local
      K extent rightPhysical links right hright link hlink
    have hleftBounded := (List.mem_filter.mp hleftLocal).1
    have hrightBounded := (List.mem_filter.mp hrightLocal).1
    apply edgeLabelling_eq_of_word_eq_of_supported edges
    · exact (boundedEdgeLabellings_sound
        (linkAuxiliaryCutoff K) edges
        (slabFusionWitnessAssignmentAt link left) hleftBounded).2
    · exact (boundedEdgeLabellings_sound
        (linkAuxiliaryCutoff K) edges
        (slabFusionWitnessAssignmentAt link right) hrightBounded).2
    · exact hword
  calc
    left = slabFusionWitnessAssignmentFrom links
        (fun link => slabFusionWitnessAssignmentAt link left) :=
      (slabFusionWitnessAssignmentFrom_at_eq K extent leftPhysical
        links left (boundaryCompleteSlabLinks_nodup extent) hleft).symm
    _ = slabFusionWitnessAssignmentFrom links
        (fun link => slabFusionWitnessAssignmentAt link right) := by
      unfold slabFusionWitnessAssignmentFrom
      apply List.map_congr_left
      intro link hlink
      congr 1
      exact hlookup link hlink
    _ = right := slabFusionWitnessAssignmentFrom_at_eq
      K extent rightPhysical links right
        (boundaryCompleteSlabLinks_nodup extent) hright

/-! ## 3. The decidable target key and its exactness -/

/-- A complete expanded target represented only by decidable finite words. -/
structure SlabExpandedFineTargetKey : Type where
  physicalWord : List Nat
  auxiliaryWords : List (List Nat)
  deriving DecidableEq

/-- Encode one physical/auxiliary pair on the exact production supports. -/
def slabExpandedFineTargetKey
    (D : SlabPhysicalData) (physical : SlabLabelling)
    (assignment : SlabFusionWitnessAssignment) :
    SlabExpandedFineTargetKey where
  physicalWord := finiteEdgeLabellingWord D.faceEdges physical
  auxiliaryWords := slabFusionWitnessAssignmentWords D.extent assignment

/-- The decidable key is injective on the literal expanded production
carrier. -/
theorem slabExpandedFineTargetKey_eq_source_eq
    (D : SlabPhysicalData)
    {left right : SlabLabelling × SlabFusionWitnessAssignment}
    (hleft : left ∈ slabExpandedFineSources D)
    (hright : right ∈ slabExpandedFineSources D)
    (hkey : slabExpandedFineTargetKey D left.1 left.2 =
      slabExpandedFineTargetKey D right.1 right.2) :
    left = right := by
  have hleftMem := mem_slabExpandedFineSources_iff.mp hleft
  have hrightMem := mem_slabExpandedFineSources_iff.mp hright
  have hphysicalWord :=
    congrArg SlabExpandedFineTargetKey.physicalWord hkey
  have hauxiliaryWords :=
    congrArg SlabExpandedFineTargetKey.auxiliaryWords hkey
  have hleftSound := boundedEdgeLabellings_sound
    D.cutoff D.faceEdges left.1 hleftMem.1
  have hrightSound := boundedEdgeLabellings_sound
    D.cutoff D.faceEdges right.1 hrightMem.1
  have hphysical : left.1 = right.1 :=
    edgeLabelling_eq_of_word_eq_of_supported D.faceEdges
      left.1 right.1 hleftSound.2 hrightSound.2 hphysicalWord
  have hassignment : left.2 = right.2 :=
    slabFusionWitnessAssignment_eq_of_words_eq
      D.cutoff D.extent left.1 right.1 left.2 right.2
      hleftMem.2 hrightMem.2 hauxiliaryWords
  exact Prod.ext hphysical hassignment

/-- The finite decidable carrier of all expanded production targets. -/
def slabExpandedFineTargetKeys (D : SlabPhysicalData) :
    List SlabExpandedFineTargetKey :=
  (slabExpandedFineSources D).map fun source =>
    slabExpandedFineTargetKey D source.1 source.2

/-- Exact target keys carry no duplicate multiplicity. -/
theorem slabExpandedFineTargetKeys_nodup (D : SlabPhysicalData) :
    (slabExpandedFineTargetKeys D).Nodup := by
  unfold slabExpandedFineTargetKeys
  apply nodup_map_of_injOn
  · exact slabExpandedFineSources_nodup D
  · intro left hleft right hright hkey
    exact slabExpandedFineTargetKey_eq_source_eq D hleft hright hkey

/-! ## 4. Every accepted component target has one of these keys -/

/-- An accepted rooted component lowers an actual expanded source to another
member of the literal expanded production carrier. -/
theorem SlabFusionWitnessFaceStrandSeed.lowerTarget_mem_expanded
    (D : SlabPhysicalData)
    {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn D.cutoff D.extent physical
        (boundaryCompleteSlabLinks D.extent)}
    (hphysical : physical ∈ D.physicalLabellings)
    (seed : SlabFusionWitnessFaceStrandSeed D.cutoff D.extent physical
      (boundaryCompleteSlabLinks D.extent) assignment hassignment) :
    (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed,
        SlabFusionWitnessFaceStrandSeed.lowerAssignment seed) ∈
      slabExpandedFineSources D := by
  apply mem_slabExpandedFineSources_iff.mpr
  constructor
  · unfold SlabPhysicalData.physicalLabellings SlabPhysicalData.faceEdges
      SlabFusionWitnessFaceStrandSeed.lowerPhysical
      lowerSlabPhysicalByFaceStrandSelection
    exact lowerEdgeLabellingBy_mem_bounded
      (slabPhysicalFaceEdges D.extent) hphysical
  · exact SlabFusionWitnessFaceStrandSeed.lowerAssignment_mem seed

/-- Therefore the finite key of every accepted rooted component target is
literally present in the duplicate-free target-key carrier. -/
theorem SlabFusionWitnessFaceStrandSeed.lowerTargetKey_mem
    (D : SlabPhysicalData)
    {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn D.cutoff D.extent physical
        (boundaryCompleteSlabLinks D.extent)}
    (hphysical : physical ∈ D.physicalLabellings)
    (seed : SlabFusionWitnessFaceStrandSeed D.cutoff D.extent physical
      (boundaryCompleteSlabLinks D.extent) assignment hassignment) :
    slabExpandedFineTargetKey D
        (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed)
        (SlabFusionWitnessFaceStrandSeed.lowerAssignment seed) ∈
      slabExpandedFineTargetKeys D := by
  unfold slabExpandedFineTargetKeys
  exact List.mem_map.mpr
    ⟨(SlabFusionWitnessFaceStrandSeed.lowerPhysical seed,
      SlabFusionWitnessFaceStrandSeed.lowerAssignment seed),
      SlabFusionWitnessFaceStrandSeed.lowerTarget_mem_expanded
        D hphysical seed, rfl⟩

#print axioms finiteEdgeLabellingWord
#print axioms edgeLabelling_eq_of_word_eq_of_supported
#print axioms slabFusionWitnessAssignmentWords
#print axioms slabFusionWitnessAssignment_eq_of_words_eq
#print axioms SlabExpandedFineTargetKey
#print axioms slabExpandedFineTargetKey
#print axioms slabExpandedFineTargetKey_eq_source_eq
#print axioms slabExpandedFineTargetKeys
#print axioms slabExpandedFineTargetKeys_nodup
#print axioms SlabFusionWitnessFaceStrandSeed.lowerTarget_mem_expanded
#print axioms SlabFusionWitnessFaceStrandSeed.lowerTargetKey_mem

end YMGap.Continuum.CompactDualSlabExpandedTargetKey
