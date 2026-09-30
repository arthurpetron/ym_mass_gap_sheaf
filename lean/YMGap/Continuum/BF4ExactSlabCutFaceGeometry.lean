/-
# Local geometry of a physical slab time-layer cut

For a selected set of physical links, a crossing plaquette has boundary links
on both sides of the selection. If every link strictly below time `t` is
selected and every link strictly above `t` is unselected, every crossing
plaquette is based at time `t` or `t-1`. Links based exactly at `t` are
unrestricted. This is a finite geometric statement about the original slab
plaquettes; it asserts no estimate for the action or a replica observable.
-/

import YMGap.Continuum.Z4HalfTimeReflectionGeometry

namespace YMGap.Continuum.BF4ExactSlabCutFaceGeometry

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-- Whether a physical plaquette has at least one selected and one
unselected boundary link. -/
def cutCrossingFace (selected : List Z4Link) (face : Z4Plaq) : Bool :=
  (edgesOf face).any (fun link => decide (link ∈ selected)) &&
    (edgesOf face).any (fun link => decide (link ∉ selected))

/-- The actual slab faces whose boundaries cross the selected-link set. -/
def cutCrossingFaces (extent : Nat) (selected : List Z4Link) : List Z4Plaq :=
  (boundaryCompleteSlabPlaquettes extent).filter
    (fun face => cutCrossingFace selected face)

/-- Membership in the crossing-face list retains the original slab face and
is exactly the two-sided boundary-incidence test. -/
theorem mem_cutCrossingFaces_iff (extent : Nat) (selected : List Z4Link)
    (face : Z4Plaq) :
    face ∈ cutCrossingFaces extent selected ↔
      face ∈ boundaryCompleteSlabPlaquettes extent ∧
        cutCrossingFace selected face = true := by
  simp [cutCrossingFaces]

/-- Every edge of a coordinate plaquette is based at its time coordinate or
the next time coordinate. -/
theorem face_time_le_edge_time_le_succ {face : Z4Plaq} {link : Z4Link}
    (hedge : link ∈ edgesOf face) :
    face.1.2.2.2 ≤ link.1.2.2.2 ∧
      link.1.2.2.2 ≤ face.1.2.2.2 + 1 := by
  obtain ⟨⟨x0, x1, x2, time⟩, plane⟩ := face
  cases plane <;>
    simp only [edgesOf, dirsOf, addE, List.mem_cons,
      List.not_mem_nil, or_false] at hedge <;>
    rcases hedge with rfl | rfl | rfl | rfl <;>
    simp [addE]

/-- A time-layer cut can only be crossed by faces in its two adjacent
plaquette layers. This permits an arbitrary selection of links at time `t`.
-/
theorem cutCrossingFaces_time_locality
    (extent time : Nat) (selected : List Z4Link)
    (hbelow : ∀ link, link ∈ boundaryCompleteSlabLinks extent →
      link.1.2.2.2 < time → link ∈ selected)
    (habove : ∀ link, link ∈ boundaryCompleteSlabLinks extent →
      time < link.1.2.2.2 → link ∉ selected)
    {face : Z4Plaq} (hface : face ∈ cutCrossingFaces extent selected) :
    time ≤ face.1.2.2.2 + 1 ∧ face.1.2.2.2 ≤ time := by
  have hmem := (mem_cutCrossingFaces_iff extent selected face).mp hface
  have hcross : cutCrossingFace selected face = true := hmem.2
  have hcross' := (Bool.and_eq_true _ _).mp hcross
  have hs := List.any_eq_true.mp hcross'.1
  have hu := List.any_eq_true.mp hcross'.2
  obtain ⟨selectedLink, hselectedEdge, hselectedBool⟩ := hs
  obtain ⟨unselectedLink, hunselectedEdge, hunselectedBool⟩ := hu
  have hselected : selectedLink ∈ selected := of_decide_eq_true hselectedBool
  have hunselected : unselectedLink ∉ selected := of_decide_eq_true hunselectedBool
  have hselectedPhysical : selectedLink ∈ boundaryCompleteSlabLinks extent :=
    (mem_boundaryCompleteSlabLinks_iff extent selectedLink).mpr
      ⟨face, hmem.1, hselectedEdge⟩
  have hunselectedPhysical : unselectedLink ∈ boundaryCompleteSlabLinks extent :=
    (mem_boundaryCompleteSlabLinks_iff extent unselectedLink).mpr
      ⟨face, hmem.1, hunselectedEdge⟩
  have hselectedTimes := face_time_le_edge_time_le_succ hselectedEdge
  have hunselectedTimes := face_time_le_edge_time_le_succ hunselectedEdge
  constructor
  · by_cases htime : time ≤ face.1.2.2.2 + 1
    · exact htime
    · have hfaceBefore : face.1.2.2.2 + 1 < time := by omega
      have hlinkBefore : unselectedLink.1.2.2.2 < time :=
        Nat.lt_of_le_of_lt hunselectedTimes.2 hfaceBefore
      have hforced := hbelow unselectedLink hunselectedPhysical hlinkBefore
      exact False.elim (hunselected hforced)
  · by_cases htime : face.1.2.2.2 ≤ time
    · exact htime
    · have htimeBefore : time < face.1.2.2.2 := by omega
      have hlinkAfter : time < selectedLink.1.2.2.2 :=
        Nat.lt_of_lt_of_le htimeBefore hselectedTimes.1
      have hforced := habove selectedLink hselectedPhysical hlinkAfter
      exact False.elim (hforced hselected)

end YMGap.Continuum.BF4ExactSlabCutFaceGeometry

#print axioms YMGap.Continuum.BF4ExactSlabCutFaceGeometry.cutCrossingFace
#print axioms YMGap.Continuum.BF4ExactSlabCutFaceGeometry.cutCrossingFaces
#print axioms YMGap.Continuum.BF4ExactSlabCutFaceGeometry.mem_cutCrossingFaces_iff
#print axioms YMGap.Continuum.BF4ExactSlabCutFaceGeometry.face_time_le_edge_time_le_succ
#print axioms YMGap.Continuum.BF4ExactSlabCutFaceGeometry.cutCrossingFaces_time_locality
