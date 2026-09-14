/-
# A retained connected selection crosses every intervening time cut

If no selected plaquette crosses time t, partition the actual selected
face indices by base time <= t. All links of the first region are at
time <= t and all links of the second are at time > t. This supplies an
explicit separating cut, contradicting the existing separator filter.
No extracted path, component oracle, or representation estimate is used.
-/

import YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
import YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
import YMGap.Continuum.FiniteSelectionOrder
import YMGap.Continuum.Z4TemporalCutParityMinimum

namespace YMGap.Continuum.BF4ExactSlabConnectedTemporalCrossing

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSelectionSeparation
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.FiniteSelectionOrder
open YMGap.Continuum.Z4TemporalCutParityMinimum
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

theorem face_link_time_lower (face : Z4Plaq) (link : Z4Link) (hl : link ∈ edgesOf face) :
    face.1.2.2.2 ≤ link.1.2.2.2 := by
  rcases face with ⟨⟨a,b,c,s⟩,p⟩
  cases p <;> simp only [edgesOf, dirsOf, addE, List.mem_cons, List.not_mem_nil, or_false] at hl
  all_goals rcases hl with rfl | rfl | rfl | rfl
  all_goals dsimp only; omega

theorem face_link_below (time : Nat) (face : Z4Plaq)
    (hn : crosses time face = false) (hf : face.1.2.2.2 ≤ time)
    (link : Z4Link) (hl : link ∈ edgesOf face) : link.1.2.2.2 ≤ time := by
  have hc : ¬((dirsOf face.2).2 = Dir4.x3 ∧ face.1.2.2.2 = time) := of_decide_eq_false hn
  rcases face with ⟨⟨a,b,c,s⟩,p⟩
  cases p <;> simp only [edgesOf, dirsOf, addE, List.mem_cons, List.not_mem_nil, or_false] at hl
  all_goals rcases hl with rfl | rfl | rfl | rfl
  all_goals simp only [dirsOf, true_and] at hc
  all_goals dsimp only at hf ⊢; omega

def belowIds (extent time : Nat) (selected : List Nat) : List Nat :=
  selected.filter (fun id => decide ((slabPlaquetteAt extent id).1.2.2.2 ≤ time))

/-- The cut itself is computed; the no-crossing premise proves its separation. -/
def temporalSeparator (extent time : Nat) (selected : List Nat) (left right : List Z4Link)
    (hn : ∀ id, id ∈ selected → crosses time (slabPlaquetteAt extent id) = false)
    (hl : ∀ link, link ∈ left → link.1.2.2.2 ≤ time)
    (hr : ∀ link, link ∈ right → time < link.1.2.2.2) : Separator extent left right selected where
  cut := belowIds extent time selected
  disjoint := by
    intro link hleft hright
    have hb : link.1.2.2.2 ≤ time := by
      rcases List.mem_append.mp hleft with hp | hp
      · exact hl link hp
      · obtain ⟨id,hi,he⟩ := List.mem_flatMap.mp hp
        have hs := (List.mem_filter.mp hi).1
        have hc := of_decide_eq_true (List.mem_filter.mp hi).2
        have ht := of_decide_eq_true (List.mem_filter.mp hc).2
        exact face_link_below time _ (hn id hs) ht link he
    have ha : time < link.1.2.2.2 := by
      rcases List.mem_append.mp hright with hp | hp
      · exact hr link hp
      · obtain ⟨id,hi,he⟩ := List.mem_flatMap.mp hp
        have hs := (List.mem_filter.mp hi).1
        have hcut : id ∉ belowIds extent time selected := by
          intro hm
          have hh := (List.mem_filter.mp hi).2
          simp only [decide_eq_true hm, Bool.not_true, Bool.false_eq_true] at hh
        have ht : ¬(slabPlaquetteAt extent id).1.2.2.2 ≤ time :=
          fun hh => hcut (List.mem_filter.mpr ⟨hs,decide_eq_true hh⟩)
        have hb := face_link_time_lower _ link he
        omega
    omega

def crossingIds (extent time : Nat) (selected : List Nat) : List Nat :=
  selected.filter (fun id => crosses time (slabPlaquetteAt extent id))

theorem retained_crossing_nonempty {extent : Nat} {left right : List Z4Link} {ids selected : List Nat}
    (hs : selected ∈ connectedSelections extent left right ids) (time : Nat)
    (hl : ∀ link, link ∈ left → link.1.2.2.2 ≤ time)
    (hr : ∀ link, link ∈ right → time < link.1.2.2.2) :
    crossingIds extent time selected ≠ [] := by
  intro he
  have hn (id : Nat) (hi : id ∈ selected) : crosses time (slabPlaquetteAt extent id) = false := by
    cases hc : crosses time (slabPlaquetteAt extent id) with
    | false => rfl
    | true =>
      have hm : id ∈ crossingIds extent time selected := List.mem_filter.mpr ⟨hi,hc⟩
      rw [he] at hm
      exact False.elim (List.not_mem_nil hm)
  exact retained_no_separating_cut hs (belowIds extent time selected) (filter_selected _ _)
    (temporalSeparator extent time selected left right hn hl hr).disjoint

theorem endpoint_link_time (margin offset : Nat) (link : Z4Link)
    (hl : link ∈ edgesOf (sliceFace margin offset)) : link.1.2.2.2 = margin + offset := by
  simp only [sliceFace, edgesOf, dirsOf, addE, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl <;> rfl

theorem shifted_probe_crossing_nonempty {margin : Nat} {ids selected : List Nat}
    (hs : selected ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) ids) (time : Nat) (hlo : margin ≤ time) (hhi : time < margin+3) :
    crossingIds (responseExtent margin) time selected ≠ [] :=
  retained_crossing_nonempty hs time
    (fun link hl => by rw [endpoint_link_time margin 0 link hl, Nat.add_zero]; exact hlo)
    (fun link hr => by rw [endpoint_link_time margin 3 link hr]; exact hhi)

end YMGap.Continuum.BF4ExactSlabConnectedTemporalCrossing

#print axioms YMGap.Continuum.BF4ExactSlabConnectedTemporalCrossing.face_link_time_lower
#print axioms YMGap.Continuum.BF4ExactSlabConnectedTemporalCrossing.face_link_below
#print axioms YMGap.Continuum.BF4ExactSlabConnectedTemporalCrossing.belowIds
#print axioms YMGap.Continuum.BF4ExactSlabConnectedTemporalCrossing.temporalSeparator
#print axioms YMGap.Continuum.BF4ExactSlabConnectedTemporalCrossing.crossingIds
#print axioms YMGap.Continuum.BF4ExactSlabConnectedTemporalCrossing.retained_crossing_nonempty
#print axioms YMGap.Continuum.BF4ExactSlabConnectedTemporalCrossing.endpoint_link_time
#print axioms YMGap.Continuum.BF4ExactSlabConnectedTemporalCrossing.shifted_probe_crossing_nonempty
