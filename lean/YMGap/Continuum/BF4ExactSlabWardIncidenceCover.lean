/-
# Exact fourfold coverage by all physical slab links

Attaching membership witnesses to the duplicate-free complete slab-link list
gives the canonical family of all physical links.  Every physical plaquette
has exactly its four boundary links in this family.  Finite Fubini therefore
counts every physical-face weight exactly four times.

This is finite incidence bookkeeping only.  The coefficient signs are kept
until the explicit square in the final specialization; no action or analytic
estimate is introduced.
-/

import YMGap.Continuum.BF4ExactSlabWardIncidenceSum

namespace YMGap.Continuum.BF4ExactSlabWardIncidenceCover

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabWardFamilyCost
open YMGap.Continuum.BF4ExactSlabWardIncidenceSum
open YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4SpinDependentIncidenceProductBound
open YMGap.Continuum.Z4UnitCubeIncidenceParity

local infix:50 " ≈ " => Q'.eqv

/-- The canonical duplicate-free list of all slab links, retaining a witness
that each link belongs to the physical carrier. -/
def allPhysicalLinks (extent : Nat) : List (PhysicalLink extent) :=
  (boundaryCompleteSlabLinks extent).attach

theorem allPhysicalLinks_nodup (extent : Nat) :
    (allPhysicalLinks extent).Nodup := by
  unfold allPhysicalLinks
  exact attach_nodup_of_nodup _ (boundaryCompleteSlabLinks_nodup extent)

private theorem faceRow_all_map_perm (extent id : Nat)
    (hid : id ∈ slabPhysicalFaceEdges extent) :
    ((faceRow extent id (allPhysicalLinks extent)).map
        (fun link => link.val)).Perm
      (edgesOf (slabPlaquetteAt extent id)) := by
  let row := faceRow extent id (allPhysicalLinks extent)
  have hrowNodup : row.Nodup :=
    List.filter_sublist.nodup (allPhysicalLinks_nodup extent)
  have hmappedNodup : (row.map (fun link => link.val)).Nodup :=
    nodup_map_of_injOn (fun link : PhysicalLink extent => link.val) row hrowNodup
      (fun left _ right _ heq => Subtype.ext heq)
  apply Z4CanonicalPolymerUniverse.perm_of_nodup_mem_iff
  · exact hmappedNodup
  · exact edgesOf_nodup _
  · intro edge
    constructor
    · intro hedge
      obtain ⟨link, hlink, rfl⟩ := List.mem_map.mp hedge
      exact of_decide_eq_true (List.mem_filter.mp hlink).2
    · intro hedge
      have hface := slabPlaquetteAt_mem hid
      have hphysical : edge ∈ boundaryCompleteSlabLinks extent :=
        (mem_boundaryCompleteSlabLinks_iff extent edge).mpr
          ⟨slabPlaquetteAt extent id, hface, hedge⟩
      let link : PhysicalLink extent := ⟨edge, hphysical⟩
      have hattach : link ∈ allPhysicalLinks extent := by
        unfold allPhysicalLinks
        exact List.mem_attach _ link
      have hrow : link ∈ faceRow extent id (allPhysicalLinks extent) :=
        List.mem_filter.mpr ⟨hattach, decide_eq_true hedge⟩
      exact List.mem_map.mpr ⟨link, hrow, rfl⟩

/-- Every physical face has exactly four entries in the all-link incidence
row; the subtype witnesses add no duplicates. -/
theorem faceRow_all_length (extent id : Nat)
    (hid : id ∈ slabPhysicalFaceEdges extent) :
    (faceRow extent id (allPhysicalLinks extent)).length = 4 := by
  have hlength := (faceRow_all_map_perm extent id hid).length_eq
  simpa only [List.length_map, edgesOf_length] using hlength

private theorem inner_incident_eq_mask (extent : Nat)
    (weight : Nat → Q') (link : PhysicalLink extent) :
    listQSum weight (incidentIds extent link.val) ≈
      listQSum
        (finiteMaskedValue
          (fun id => decide (link.val ∈ edgesOf (slabPlaquetteAt extent id)))
          weight)
        (slabPhysicalFaceEdges extent) := by
  unfold incidentIds
  exact Q'.eqv_symm
    (listQSum_finiteMaskedValue_eqv_filter
      (fun id => decide (link.val ∈ edgesOf (slabPlaquetteAt extent id)))
      weight (slabPhysicalFaceEdges extent))

private theorem outer_face_eq_row (extent id : Nat)
    (weight : Nat → Q') (xs : List (PhysicalLink extent)) :
    listQSum
        (fun link => finiteMaskedValue
          (fun face => decide (link.val ∈ edgesOf (slabPlaquetteAt extent face)))
          weight id)
        xs ≈
      listQSum (fun _ : PhysicalLink extent => weight id)
        (faceRow extent id xs) := by
  change listQSum
      (finiteMaskedValue
        (fun link : PhysicalLink extent =>
          decide (link.val ∈ edgesOf (slabPlaquetteAt extent id)))
        (fun _ => weight id)) xs ≈ _
  exact listQSum_finiteMaskedValue_eqv_filter _ _ xs

private theorem faceRow_all_weight (extent id : Nat)
    (hid : id ∈ slabPhysicalFaceEdges extent) (weight : Q') :
    listQSum (fun _ : PhysicalLink extent => weight)
        (faceRow extent id (allPhysicalLinks extent)) ≈
      Q'.ofNat 4 * weight := by
  exact Q'.eqv_trans _ (weight * Q'.ofNat (faceRow extent id (allPhysicalLinks extent)).length) _
    (RationalFiniteSparseGram.listQSum_const weight _)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left weight _ _
        (Q'.eqv_of_eq (congrArg Q'.ofNat (faceRow_all_length extent id hid))))
      (Q'.mul_comm_eqv weight (Q'.ofNat 4)))

/-- Finite exact Fubini: the canonical family of all witnessed physical links
counts every physical face precisely once for each of its four edges. -/
theorem incidence_sum_eq_four (extent : Nat) (weight : Nat → Q') :
    listQSum
        (fun link => listQSum weight (incidentIds extent link.val))
        (allPhysicalLinks extent) ≈
      Q'.ofNat 4 * listQSum weight (slabPhysicalFaceEdges extent) := by
  let masked : PhysicalLink extent → Nat → Q' := fun link id =>
    finiteMaskedValue
      (fun face => decide (link.val ∈ edgesOf (slabPlaquetteAt extent face)))
      weight id
  have hleft : listQSum
      (fun link => listQSum weight (incidentIds extent link.val))
      (allPhysicalLinks extent) ≈
      listQSum (fun id => listQSum (fun link => masked link id)
        (allPhysicalLinks extent)) (slabPhysicalFaceEdges extent) := by
    exact Q'.eqv_trans _ _ _
      (listQSum_congr_on _ _ (allPhysicalLinks extent)
        (fun link _ => inner_incident_eq_mask extent weight link))
      (Q'.eqv_symm (listQSum_swap masked (allPhysicalLinks extent)
        (slabPhysicalFaceEdges extent)))
  have hrows : listQSum (fun id => listQSum (fun link => masked link id)
      (allPhysicalLinks extent)) (slabPhysicalFaceEdges extent) ≈
      listQSum (fun id => Q'.ofNat 4 * weight id)
        (slabPhysicalFaceEdges extent) :=
    listQSum_congr_on _ _ _ (fun id hid =>
      Q'.eqv_trans _ _ _
        (outer_face_eq_row extent id weight (allPhysicalLinks extent))
        (faceRow_all_weight extent id hid (weight id)))
  exact Q'.eqv_trans _ _ _ hleft
    (Q'.eqv_trans _ _ _ hrows
      (listQSum_mul_left (Q'.ofNat 4) weight
        (slabPhysicalFaceEdges extent)))

/-- Exact fourfold coverage specialized to the squared coefficients of the
literal signed plaquette observable. -/
theorem coefficient_square_incidence_eq_four (extent : Nat) (c : Nat → Q') :
    listQSum
        (fun link => listQSum (fun id => c id * c id)
          (incidentIds extent link.val))
        (allPhysicalLinks extent) ≈
      Q'.ofNat 4 * listQSum (fun id => c id * c id)
        (slabPhysicalFaceEdges extent) :=
  incidence_sum_eq_four extent (fun id => c id * c id)

end YMGap.Continuum.BF4ExactSlabWardIncidenceCover

#print axioms YMGap.Continuum.BF4ExactSlabWardIncidenceCover.allPhysicalLinks
#print axioms YMGap.Continuum.BF4ExactSlabWardIncidenceCover.allPhysicalLinks_nodup
#print axioms YMGap.Continuum.BF4ExactSlabWardIncidenceCover.faceRow_all_length
#print axioms YMGap.Continuum.BF4ExactSlabWardIncidenceCover.incidence_sum_eq_four
#print axioms YMGap.Continuum.BF4ExactSlabWardIncidenceCover.coefficient_square_incidence_eq_four
