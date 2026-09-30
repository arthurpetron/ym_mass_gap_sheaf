/-
# Exact spatial collar geometry for an arbitrary selected link list

The spatial faces are partitioned, in their original order up to `Perm`, into
those touching at least one selected link and the complementary faces. Each
selected link has at most six incident plaquettes, so the collar has at most
six faces per selected-list entry. This is a finite geometric count only.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
import YMGap.Continuum.Z4SpinDependentIncidenceProductBound
import YMGap.Continuum.CayleyPruferInjection

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLocalCollarGeometry

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4SpinDependentIncidenceProductBound (edgesOf_length)
open YMGap.Continuum.CayleyPruferInjection (nodup_subset_length_le)

/-- Spatial faces incident to at least one link in `selected`. -/
def spatialCollarFaces (width : Nat) (selected : List Z4Link) : List Z4Plaq :=
  (spatialFaces width).filter fun face =>
    selected.any fun link => decide (link ∈ edgesOf face)

/-- Spatial faces incident to no link in `selected`. -/
def spatialCollarComplementFaces (width : Nat) (selected : List Z4Link) : List Z4Plaq :=
  (spatialFaces width).filter fun face =>
    !(selected.any fun link => decide (link ∈ edgesOf face))

/-- Every spatial face lies in exactly one side of the literal filter split. -/
theorem spatialCollar_partition (width : Nat) (selected : List Z4Link) :
    (spatialCollarFaces width selected ++ spatialCollarComplementFaces width selected).Perm
      (spatialFaces width) := by
  exact List.filter_append_perm _ _

/-- Membership in the collar is exactly spatial-face membership plus a selected
boundary link. -/
theorem spatialCollarFaces_mem_iff (width : Nat) (selected : List Z4Link)
    (face : Z4Plaq) :
    face ∈ spatialCollarFaces width selected ↔
      face ∈ spatialFaces width ∧ ∃ link, link ∈ selected ∧ link ∈ edgesOf face := by
  unfold spatialCollarFaces
  rw [List.mem_filter]
  constructor
  · rintro ⟨hface, hany⟩
    obtain ⟨link, hlink, hinc⟩ := List.any_eq_true.mp hany
    exact ⟨hface, link, hlink, of_decide_eq_true hinc⟩
  · rintro ⟨hface, link, hlink, hinc⟩
    refine ⟨hface, List.any_eq_true.mpr ⟨link, hlink, ?_⟩⟩
    exact decide_eq_true hinc

/-- Membership in the complement means every selected link misses the face. -/
theorem spatialCollarComplementFaces_mem_iff (width : Nat) (selected : List Z4Link)
    (face : Z4Plaq) :
    face ∈ spatialCollarComplementFaces width selected ↔
      face ∈ spatialFaces width ∧ ∀ link, link ∈ selected → link ∉ edgesOf face := by
  unfold spatialCollarComplementFaces
  rw [List.mem_filter]
  constructor
  · rintro ⟨hface, hnone⟩
    refine ⟨hface, ?_⟩
    intro link hlink hinc
    have hany : selected.any (fun l => decide (l ∈ edgesOf face)) = true :=
      List.any_eq_true.mpr ⟨link, hlink, decide_eq_true hinc⟩
    rw [hany] at hnone
    cases hnone
  · rintro ⟨hface, hmiss⟩
    refine ⟨hface, ?_⟩
    cases hany : selected.any (fun l => decide (l ∈ edgesOf face)) with
    | false => rfl
    | true =>
      obtain ⟨link, hlink, hinc⟩ := List.any_eq_true.mp hany
      exact False.elim (hmiss link hlink (of_decide_eq_true hinc))

/-- The complementary faces omit every selected link. -/
theorem spatialCollarComplement_omits (width : Nat) (selected : List Z4Link)
    {face : Z4Plaq} (hface : face ∈ spatialCollarComplementFaces width selected)
    {link : Z4Link} (hlink : link ∈ selected) :
    link ∉ edgesOf face :=
  (spatialCollarComplementFaces_mem_iff width selected face).mp hface |>.2 link hlink

private def selectedEdgePlaquettes (selected : List Z4Link) : List Z4Plaq :=
  selected.flatMap fun link => edgePlaqs link.1 link.2

private theorem selectedEdgePlaquettes_length_le (selected : List Z4Link) :
    (selectedEdgePlaquettes selected).length ≤ 6 * selected.length := by
  induction selected with
  | nil => simp [selectedEdgePlaquettes]
  | cons link rest ih =>
      simp only [selectedEdgePlaquettes, List.flatMap_cons, List.length_append,
        edgePlaqs_length, List.length_cons] at *
      omega

/-- The collar count is at most six times the number of selected-list entries.
Repeated selected links are permitted and only make this bound looser. -/
theorem spatialCollarFaces_length_le (width : Nat) (selected : List Z4Link) :
    (spatialCollarFaces width selected).length ≤ 6 * selected.length := by
  have hn : (spatialCollarFaces width selected).Nodup :=
    List.filter_sublist.nodup (spatialFaces_nodup width)
  have hsub : ∀ face, face ∈ spatialCollarFaces width selected →
      face ∈ selectedEdgePlaquettes selected := by
    intro face hface
    obtain ⟨_, link, hlink, hinc⟩ :=
      (spatialCollarFaces_mem_iff width selected face).mp hface
    apply List.mem_flatMap.mpr
    refine ⟨link, hlink, ?_⟩
    exact edge_complete face link.1 link.2 hinc
  exact Nat.le_trans
    (nodup_subset_length_le _ _ hn hsub)
    (selectedEdgePlaquettes_length_le selected)

/-- A single plaquette's four boundary links generate a collar of at most 24
spatial faces. -/
theorem spatialCollarFaces_edgesOf_length_le_twenty_four
    (width : Nat) (face : Z4Plaq) :
    (spatialCollarFaces width (edgesOf face)).length ≤ 24 := by
  have h := spatialCollarFaces_length_le width (edgesOf face)
  rw [edgesOf_length] at h
  omega

#print axioms spatialCollarFaces
#print axioms spatialCollarComplementFaces
#print axioms spatialCollar_partition
#print axioms spatialCollarFaces_mem_iff
#print axioms spatialCollarComplementFaces_mem_iff
#print axioms spatialCollarComplement_omits
#print axioms spatialCollarFaces_length_le
#print axioms spatialCollarFaces_edgesOf_length_le_twenty_four

end YMGap.Continuum.BF4ExactSlabFixedSpatialLocalCollarGeometry
