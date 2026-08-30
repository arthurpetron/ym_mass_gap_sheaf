/-
# Cutoff persistence of accepted slab fine-intertwiner assignments

The canonical trivalent admissibility predicate for a fixed physical link
does not depend on the representation cutoff.  Enlarging the cutoff only
enlarges the explicitly enumerated auxiliary-label window.  Hence every
accepted local auxiliary at a smaller cutoff remains accepted at a larger
one, and structural Cartesian assembly preserves the same complete global
assignment.

This is the monotone embedding compiler needed to reuse a low-spin local
gadget at every larger cutoff.  It proves qualitative persistence of an
existing witness, not a cutoff-uniform probability or weight lower bound.

Constructive contract: bounded-list soundness/completeness and structural
finite-list recursion only; no `Classical`, choice, `native_decide`, `sorry`,
new axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabFineIntertwinerWitness

namespace YMGap.Continuum.CompactDualSlabFineIntertwinerCutoffPersistence

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

/-! ## 1. Local cutoff persistence -/

/-- A literal accepted link auxiliary remains in the same filtered
admissibility carrier when the representation cutoff is enlarged. -/
theorem slabLinkFusionWitnesses_mem_of_cutoff_le
    {base later extent : Nat} (hcutoff : base ≤ later)
    (physical : SlabLabelling) (link : SlabLink)
    (auxiliary : SlabLabelling)
    (hauxiliary : auxiliary ∈
      slabLinkFusionWitnesses base extent physical link) :
    auxiliary ∈ slabLinkFusionWitnesses later extent physical link := by
  unfold slabLinkFusionWitnesses at hauxiliary ⊢
  obtain ⟨hbounded, hallowed⟩ := List.mem_filter.mp hauxiliary
  apply List.mem_filter.mpr
  refine ⟨?_, hallowed⟩
  have hsound := boundedEdgeLabellings_sound
    (linkAuxiliaryCutoff base)
    (canonicalUsedAuxiliaryCoordinates
      (slabIncidentPlaqIds extent link).length)
    auxiliary hbounded
  apply boundedEdgeLabellings_complete
  · intro edge hedge
    have hold := hsound.1 edge hedge
    unfold linkAuxiliaryCutoff linkIncidenceBound at hold ⊢
    omega
  · exact hsound.2

/-! ## 2. Cartesian global persistence -/

/-- The same complete assignment occurs in the larger-cutoff Cartesian
product, with no recoding of its link or auxiliary labels. -/
theorem slabFusionWitnessAssignmentsOn_mem_of_cutoff_le
    {base later extent : Nat} (hcutoff : base ≤ later)
    (physical : SlabLabelling) (links : List SlabLink)
    (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn base extent physical links) :
    assignment ∈
      slabFusionWitnessAssignmentsOn later extent physical links := by
  induction links generalizing assignment with
  | nil =>
      simpa only [slabFusionWitnessAssignmentsOn] using hassignment
  | cons link rest ih =>
      unfold slabFusionWitnessAssignmentsOn at hassignment ⊢
      obtain ⟨auxiliary, hauxiliary, htailMap⟩ :=
        List.mem_flatMap.mp hassignment
      obtain ⟨tail, htail, heq⟩ := List.mem_map.mp htailMap
      apply List.mem_flatMap.mpr
      refine ⟨auxiliary,
        slabLinkFusionWitnesses_mem_of_cutoff_le
          hcutoff physical link auxiliary hauxiliary, ?_⟩
      apply List.mem_map.mpr
      exact ⟨tail, ih tail htail, heq⟩

/-- A raw assignment accepted at any smaller cutoff on `D`'s exact slab
geometry belongs to `D`'s production global witness carrier. -/
theorem mem_slabFineFusionWitnesses_of_mem_at_cutoff
    (D : SlabPhysicalData) {base : Nat} (hcutoff : base ≤ D.cutoff)
    (physical : SlabLabelling) (assignment : SlabFusionWitnessAssignment)
    (hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn base D.extent physical
        (boundaryCompleteSlabLinks D.extent)) :
    assignment ∈ slabFineFusionWitnesses D physical := by
  unfold slabFineFusionWitnesses
  exact slabFusionWitnessAssignmentsOn_mem_of_cutoff_le
    hcutoff physical (boundaryCompleteSlabLinks D.extent)
      assignment hassignment

#print axioms slabLinkFusionWitnesses_mem_of_cutoff_le
#print axioms slabFusionWitnessAssignmentsOn_mem_of_cutoff_le
#print axioms mem_slabFineFusionWitnesses_of_mem_at_cutoff

end YMGap.Continuum.CompactDualSlabFineIntertwinerCutoffPersistence
