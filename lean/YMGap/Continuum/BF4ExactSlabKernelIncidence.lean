/-
# Original corrected-slab link occurrence cap

The original `faceLinks` list retains all four boundary slots of every
selected face. Each face boundary is duplicate-free, so a link's literal
occurrence count equals the number of selected incident face occurrences.
For a duplicate-free physical face-id list this is at most six, using the
existing physical face-map injection and six-face link-star enumeration.

Repeated faces are allowed in the counting identity, but NOT in the cap.
No factor, link occurrence, or action multiplicity is erased. This is the
finite degree tally for multiplying original polynomial localization bounds;
it does not integrate an action or assert an entropy or spectral bound.
-/

import YMGap.Continuum.BF4ExactSlabLinkStarGeometry
import YMGap.Continuum.Z4UnitCubeIncidenceParity

namespace YMGap.Continuum.BF4ExactSlabKernelIncidence

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality (faceLinks)
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
  (incidentIds mem_incidentIds_iff incidentIds_length_le_six)
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry (occurrenceCount)
open YMGap.Continuum.Z4UnitCubeIncidenceParity (occurrenceCount_edgesOf)

private theorem count_eq_occurrence (link : Z4Link) : ∀ links : List Z4Link,
    links.count link = occurrenceCount link links
  | [] => rfl
  | edge::links => by
      by_cases h : edge = link
      · subst edge
        rw [List.count_cons_self, occurrenceCount, if_pos rfl,
          count_eq_occurrence link links]
        exact Nat.add_comm _ 1
      · rw [List.count_cons_of_ne h, occurrenceCount, if_neg h,
          Nat.zero_add, count_eq_occurrence link links]

/-- Exact multiplicity identity for the ORIGINAL flattened boundary list.
No nodup or physicality hypothesis is needed for this equality. -/
theorem faceLinks_count_eq_incident_filter (extent : Nat) (link : Z4Link) :
    ∀ ids : List Nat,
    (faceLinks extent ids).count link =
      (ids.filter (fun id => decide (link ∈ edgesOf (slabPlaquetteAt extent id)))).length
  | [] => rfl
  | id::ids => by
      change (edgesOf (slabPlaquetteAt extent id) ++ faceLinks extent ids).count link = _
      rw [List.count_append,
        count_eq_occurrence link (edgesOf (slabPlaquetteAt extent id)),
        occurrenceCount_edgesOf, faceLinks_count_eq_incident_filter extent link ids]
      by_cases h : link ∈ edgesOf (slabPlaquetteAt extent id)
      · simp only [if_pos h, List.filter_cons, decide_eq_true h,
          if_true, List.length_cons, Nat.add_comm]
      · simp only [if_neg h, List.filter_cons, decide_eq_false h,
          Bool.false_eq_true, if_false, Nat.zero_add]

/-- At most six ORIGINAL boundary-slot occurrences of any link, provided
the actual selected face identifiers are physical and have no repetitions. -/
theorem faceLinks_count_le_six (extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hnodup : ids.Nodup) (link : Z4Link) :
    (faceLinks extent ids).count link ≤ 6 := by
  rw [faceLinks_count_eq_incident_filter extent link ids]
  have hn :
      (ids.filter (fun id => decide (link ∈ edgesOf (slabPlaquetteAt extent id)))).Nodup :=
    List.filter_sublist.nodup hnodup
  have hsub := CayleyPruferInjection.nodup_subset_length_le
    (ids.filter (fun id => decide (link ∈ edgesOf (slabPlaquetteAt extent id))))
    (incidentIds extent link) hn (by
      intro id hi
      obtain ⟨hid, hedge⟩ := List.mem_filter.mp hi
      exact (mem_incidentIds_iff extent link id).mpr
        ⟨hids id hid, of_decide_eq_true hedge⟩)
  exact Nat.le_trans hsub (incidentIds_length_le_six extent link)

#print axioms faceLinks_count_eq_incident_filter
#print axioms faceLinks_count_le_six

end YMGap.Continuum.BF4ExactSlabKernelIncidence
