/-
# Volume-independent collar size on the ORIGINAL literal plaquette links

A removed face shares a concrete link with the probe or the retained core.
The existing six-plaquettes-per-link enumeration covers every such face.
Injectivity of physical slab face identifiers then gives

  |collar| <= 6 * (|probe links| + 4 * |core faces|).

Both the intersection witness and candidate cover are computed. This is a
geometric count for the existing collar, not an assumption about independent
links, a count of connected cores, or a decay theorem.
-/

import YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
import YMGap.Continuum.CayleyPruferInjection
import YMGap.Continuum.CayleyParentInj

namespace YMGap.Continuum.BF4ExactSlabCollarDegreeBound

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSelectionSeparation
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-- Search the literal lists, retaining a shared link as Type-valued data. -/
def sharedLink (right : List Z4Link) : ∀ left : List Z4Link,
    disjointTest left right = false → Σ' link : Z4Link, (link ∈ left) ×' (link ∈ right)
  | [], h => by cases h
  | link :: left, h => by
      by_cases hr : link ∈ right
      · exact ⟨link, List.mem_cons_self, hr⟩
      · have ht : disjointTest left right = false := by
          simpa only [disjointTest, List.all_cons, decide_eq_false hr, Bool.not_false, Bool.true_and] using h
        obtain ⟨other, hl, ho⟩ := sharedLink right left ht
        exact ⟨other, List.mem_cons_of_mem link hl, ho⟩

def collar_sharedLink {extent : Nat} {links : List Z4Link} {core ambient : List Nat} {id : Nat}
    (hi : id ∈ collarIds extent links core ambient) :
    Σ' link : Z4Link, (link ∈ links++faceLinks extent core) ×' (link ∈ edgesOf (slabPlaquetteAt extent id)) := by
  have hd : detachedTest extent links core id = false := by
    simpa only [Bool.not_eq_true'] using (List.mem_filter.mp hi).2
  obtain ⟨link, hl, hr⟩ := sharedLink (faceLinks extent [id]) (links++faceLinks extent core) hd
  exact ⟨link, hl, by simpa only [faceLinks, List.flatMap_cons, List.flatMap_nil, List.append_nil] using hr⟩

/-- Six candidate plaquettes for each supplied literal link. -/
def touchingPlaquettes (links : List Z4Link) : List Z4Plaq :=
  links.flatMap (fun link => edgePlaqs link.1 link.2)

theorem touchingPlaquettes_length : ∀ links : List Z4Link,
    (touchingPlaquettes links).length = 6*links.length
  | [] => rfl
  | link :: links => by
      change (edgePlaqs link.1 link.2 ++ touchingPlaquettes links).length = 6*(links.length+1)
      rw [List.length_append, edgePlaqs_length, touchingPlaquettes_length]
      omega

theorem faceLinks_length (extent : Nat) : ∀ ids : List Nat,
    (faceLinks extent ids).length = 4*ids.length
  | [] => rfl
  | id :: ids => by
      change (edgesOf (slabPlaquetteAt extent id) ++ faceLinks extent ids).length = 4*(ids.length+1)
      rw [List.length_append, faceLinks_length]
      change 4+4*ids.length = 4*(ids.length+1)
      omega

theorem collar_face_covered {extent : Nat} {links : List Z4Link} {core ambient : List Nat} {id : Nat}
    (hi : id ∈ collarIds extent links core ambient) :
    slabPlaquetteAt extent id ∈ touchingPlaquettes (links++faceLinks extent core) := by
  obtain ⟨link, hl, hr⟩ := collar_sharedLink hi
  exact List.mem_flatMap.mpr ⟨link, hl, edge_complete _ link.1 link.2 hr⟩

/-- Applies to every duplicate-free physical ambient list, with no volume
or coupling constant in the local degree bound. -/
theorem collarIds_length_le (extent : Nat) (links : List Z4Link) (core ambient : List Nat)
    (hn : ambient.Nodup) (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent) :
    (collarIds extent links core ambient).length ≤ 6*(links.length+4*core.length) := by
  have hc : (collarIds extent links core ambient).Nodup := List.filter_sublist.nodup hn
  have hm := CayleyPruferInjection.nodup_map_of_injOn (slabPlaquetteAt extent) _ hc
    (fun a ha b hb he => slabPlaquetteAt_injective_on_physical
      (hphys a (collar_mem ha)) (hphys b (collar_mem hb)) he)
  have h := CayleyPruferInjection.nodup_subset_length_le
    ((collarIds extent links core ambient).map (slabPlaquetteAt extent))
    (touchingPlaquettes (links++faceLinks extent core)) hm (by
      intro p hp
      obtain ⟨id, hi, rfl⟩ := List.mem_map.mp hp
      exact collar_face_covered hi)
  simpa only [List.length_map, touchingPlaquettes_length, List.length_append, faceLinks_length] using h

theorem full_collarIds_length_le (extent : Nat) (links : List Z4Link) (core : List Nat) :
    (collarIds extent links core (slabPhysicalFaceEdges extent)).length ≤ 6*(links.length+4*core.length) :=
  collarIds_length_le extent links core _ (CayleyParentInj.range_nodup _) (fun _ h => h)

end YMGap.Continuum.BF4ExactSlabCollarDegreeBound

#print axioms YMGap.Continuum.BF4ExactSlabCollarDegreeBound.sharedLink
#print axioms YMGap.Continuum.BF4ExactSlabCollarDegreeBound.collar_sharedLink
#print axioms YMGap.Continuum.BF4ExactSlabCollarDegreeBound.touchingPlaquettes
#print axioms YMGap.Continuum.BF4ExactSlabCollarDegreeBound.touchingPlaquettes_length
#print axioms YMGap.Continuum.BF4ExactSlabCollarDegreeBound.faceLinks_length
#print axioms YMGap.Continuum.BF4ExactSlabCollarDegreeBound.collar_face_covered
#print axioms YMGap.Continuum.BF4ExactSlabCollarDegreeBound.collarIds_length_le
#print axioms YMGap.Continuum.BF4ExactSlabCollarDegreeBound.full_collarIds_length_le
