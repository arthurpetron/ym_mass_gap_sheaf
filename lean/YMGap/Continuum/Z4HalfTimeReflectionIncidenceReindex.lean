/-
# Reflection transport of corrected-slab plaquette incidence lists

The corrected slab now has a computable involution on numerical face IDs.
This file proves that the IDs incident on an actual lattice link transport
exactly to the IDs incident on its reflected link.  The transport is a list
permutation, hence local degrees agree.

This closes the combinatorial input to reflection invariance of the local
fusion multiplicity.  The residual is now purely representation-theoretic:
the production left-associated multiplicity must be proved invariant under
the induced permutation of its external spin list (or replaced by a proved
symmetric character-integral presentation).
-/

import YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

namespace YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4LinkIdentifierFreshness

def slabIncidentPlaqIds
    (extent : Nat) (link : Z4Link) : List Nat :=
  ((enumerate (boundaryCompleteSlabPlaquettes extent)).filter
    fun indexed => decide (link ∈ edgesOf indexed.2)).map Prod.fst

theorem mem_slabIncidentPlaqIds
    {extent : Nat} {link : Z4Link} {id : Nat} :
    id ∈ slabIncidentPlaqIds extent link ↔
      ∃ plaquette : Z4Plaq,
        (id, plaquette) ∈
          enumerate (boundaryCompleteSlabPlaquettes extent) ∧
        link ∈ edgesOf plaquette := by
  simp [slabIncidentPlaqIds]

theorem slabIncidentPlaqIds_nodup
    (extent : Nat) (link : Z4Link) :
    (slabIncidentPlaqIds extent link).Nodup := by
  unfold slabIncidentPlaqIds
  exact (List.filter_sublist.map Prod.fst).nodup
    (enumerate_fst_nodup (boundaryCompleteSlabPlaquettes extent))

theorem slabIncidentPlaqId_physical
    {extent : Nat} {link : Z4Link} {id : Nat}
    (hid : id ∈ slabIncidentPlaqIds extent link) :
    id ∈ slabPhysicalFaceEdges extent := by
  obtain ⟨plaquette, hindexed, _⟩ :=
    (mem_slabIncidentPlaqIds.mp hid)
  unfold slabPhysicalFaceEdges
  exact List.mem_range.mpr (enumerate_index_lt hindexed)

/-- Forward incidence covariance: reflect both a physical link and an
incident numerical plaquette coordinate. -/
theorem slabFaceReflectId_mem_reflectedIncident
    {extent : Nat} {link : Z4Link} {id : Nat}
    (hid : id ∈ slabIncidentPlaqIds extent link) :
    slabFaceReflectId extent id ∈
      slabIncidentPlaqIds extent (timeReflectLink extent link) := by
  obtain ⟨plaquette, hindexed, hedge⟩ :=
    (mem_slabIncidentPlaqIds.mp hid)
  have hidPhysical := slabIncidentPlaqId_physical hid
  have hlookup : slabPlaquetteAt extent id = plaquette := by
    unfold slabPlaquetteAt
    exact enumerate_getD_of_mem fallbackPlaquette hindexed
  have hsourceMem := slabPlaquetteAt_mem hidPhysical
  have hsourceAdmissible :=
    ((mem_boundaryCompleteSlabPlaquettes extent _).mp hsourceMem).2
  have hreflectedEdge :=
    timeReflectLink_mem_edgesOf_timeReflectPlaquette
      hsourceAdmissible (by simpa only [hlookup] using hedge)
  have hreflectedPhysical := slabFaceReflectId_physical hidPhysical
  apply mem_slabIncidentPlaqIds.mpr
  refine ⟨slabPlaquetteAt extent (slabFaceReflectId extent id),
    slabPlaquetteAt_mem_enumerate hreflectedPhysical, ?_⟩
  rw [slabPlaquetteAt_slabFaceReflectId hidPhysical]
  exact hreflectedEdge

/-- Backward incidence covariance follows by applying the forward theorem a
second time and using both cell involutions. -/
theorem slabFaceReflectId_mem_incident_of_mem_reflected
    {extent : Nat} {link : Z4Link} {id : Nat}
    (hlink : link ∈ boundaryCompleteSlabLinks extent)
    (hid : id ∈
      slabIncidentPlaqIds extent (timeReflectLink extent link)) :
    slabFaceReflectId extent id ∈ slabIncidentPlaqIds extent link := by
  have hback := slabFaceReflectId_mem_reflectedIncident hid
  have hlinkAdmissible :=
    linkTimeAdmissible_of_mem_boundaryCompleteSlabLinks hlink
  rw [timeReflectLink_involutive extent link hlinkAdmissible] at hback
  exact hback

/-- The complete incident-ID list is transported by the numerical face
involution, up to its physically irrelevant enumeration order. -/
theorem slabIncidentPlaqIds_reflection_perm
    {extent : Nat} {link : Z4Link}
    (hlink : link ∈ boundaryCompleteSlabLinks extent) :
    ((slabIncidentPlaqIds extent link).map
        (slabFaceReflectId extent)).Perm
      (slabIncidentPlaqIds extent (timeReflectLink extent link)) := by
  apply YMGap.Continuum.Z4CanonicalPolymerUniverse.perm_of_nodup_mem_iff
  · apply nodup_map_of_injOn
      (slabFaceReflectId extent) (slabIncidentPlaqIds extent link)
      (slabIncidentPlaqIds_nodup extent link)
    intro left hleft right hright heq
    exact slabFaceReflectId_injective_on_physical
      (slabIncidentPlaqId_physical hleft)
      (slabIncidentPlaqId_physical hright) heq
  · exact slabIncidentPlaqIds_nodup _ _
  · intro id
    constructor
    · intro hid
      obtain ⟨source, hsource, hsourceEq⟩ := List.mem_map.mp hid
      rw [← hsourceEq]
      exact slabFaceReflectId_mem_reflectedIncident hsource
    · intro hid
      have hidPhysical := slabIncidentPlaqId_physical hid
      have hsource :=
        slabFaceReflectId_mem_incident_of_mem_reflected hlink hid
      exact List.mem_map.mpr
        ⟨slabFaceReflectId extent id, hsource,
          slabFaceReflectId_involutive hidPhysical⟩

theorem slabIncidentPlaqIds_reflection_length
    {extent : Nat} {link : Z4Link}
    (hlink : link ∈ boundaryCompleteSlabLinks extent) :
    (slabIncidentPlaqIds extent link).length =
      (slabIncidentPlaqIds extent
        (timeReflectLink extent link)).length := by
  have hperm := slabIncidentPlaqIds_reflection_perm hlink
  simpa only [List.length_map] using hperm.length_eq

/-- With the reflected physical labelling, the reflected link sees a spin
list that is a permutation of the original link's spin list. -/
theorem slabIncidentSpinList_reflection_perm
    (extent : Nat) (physical : Nat -> Nat)
    {link : Z4Link}
    (hlink : link ∈ boundaryCompleteSlabLinks extent) :
    ((slabIncidentPlaqIds extent link).map physical).Perm
      ((slabIncidentPlaqIds extent (timeReflectLink extent link)).map
        (reflectSlabFaceLabelling extent physical)) := by
  have hids := (slabIncidentPlaqIds_reflection_perm hlink).map
    (reflectSlabFaceLabelling extent physical)
  have hleft :
      ((slabIncidentPlaqIds extent link).map
          (slabFaceReflectId extent)).map
          (reflectSlabFaceLabelling extent physical) =
        (slabIncidentPlaqIds extent link).map physical := by
    rw [List.map_map]
    apply List.map_congr_left
    intro id hid
    simp only [Function.comp_apply, reflectSlabFaceLabelling]
    rw [slabFaceReflectId_involutive
      (slabIncidentPlaqId_physical hid)]
  rw [hleft] at hids
  exact hids

/-! ## Axiom audit -/

#print axioms slabIncidentPlaqIds_nodup
#print axioms slabIncidentPlaqId_physical
#print axioms slabFaceReflectId_mem_reflectedIncident
#print axioms slabFaceReflectId_mem_incident_of_mem_reflected
#print axioms slabIncidentPlaqIds_reflection_perm
#print axioms slabIncidentPlaqIds_reflection_length
#print axioms slabIncidentSpinList_reflection_perm

end YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
