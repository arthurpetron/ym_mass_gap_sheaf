/-
# Area count for an original time-layer replica cut

Crossing faces lie in two adjacent base-time layers. Each layer has at most
six plaquette orientations at each of the three-dimensional spatial bases.
The enumeration is the boundary-complete ORIGINAL slab, including its
endpoint spatial faces. No action estimate or gap is asserted here.
-/

import YMGap.Continuum.BF4ExactSlabCutFaceGeometry
import YMGap.Continuum.BF4ExactSlabReplicaCutLocality
import YMGap.Continuum.CayleyPruferInjection

namespace YMGap.Continuum.BF4ExactSlabReplicaCutArea

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabCutFaceGeometry
open YMGap.Continuum.BF4ExactSlabReplicaCutLocality

/-- A deliberately generous complete six-orientation layer at base time `time`.
It need not itself satisfy the temporal-face endpoint restriction. -/
def sliceCandidates (width time : Nat) : List Z4Plaq :=
  (List.range width).flatMap fun a =>
    (List.range width).flatMap fun b =>
      (List.range width).flatMap fun c =>
        z4Planes.map fun plane => ((a, b, c, time), plane)

private theorem length_flatMap_fixed {A B : Type} (xs : List A)
    (f : A → List B) (k : Nat) (h : ∀ x, (f x).length = k) :
    (xs.flatMap f).length = xs.length * k := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons,
        h, ih, Nat.succ_mul]
      omega

theorem sliceCandidates_length (width time : Nat) :
    (sliceCandidates width time).length = 6 * width ^ 3 := by
  have hc (a b : Nat) :
      ((List.range width).flatMap fun c =>
        z4Planes.map fun plane => ((a, b, c, time), plane)).length = width * 6 := by
    rw [length_flatMap_fixed _ _ 6]
    · simp
    · intro c
      simp [z4Planes]
  have hb (a : Nat) :
      ((List.range width).flatMap fun b =>
        (List.range width).flatMap fun c =>
          z4Planes.map fun plane => ((a, b, c, time), plane)).length =
        width * (width * 6) := by
    rw [length_flatMap_fixed _ _ (width * 6)]
    · simp
    · intro b
      exact hc a b
  unfold sliceCandidates
  rw [length_flatMap_fixed _ _ (width * (width * 6))]
  · simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  · intro a
    exact hb a

private theorem face_mem_sliceCandidates {width time : Nat} {face : Z4Plaq}
    (hsp : face.1.1 < width ∧ face.1.2.1 < width ∧
      face.1.2.2.1 < width)
    (htime : face.1.2.2.2 = time) :
    face ∈ sliceCandidates width time := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := face
  obtain ⟨ha, hb, hc⟩ := hsp
  change d = time at htime
  subst d
  apply List.mem_flatMap.mpr
  refine ⟨a, List.mem_range.mpr ha, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨b, List.mem_range.mpr hb, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨c, List.mem_range.mpr hc, ?_⟩
  apply List.mem_map.mpr
  refine ⟨plane, ?_, rfl⟩
  cases plane <;> simp [z4Planes]

/-- A genuine time-layer selection crosses at most two complete spatial
base layers of original faces, hence at most `12*(extent+1)^3` faces. -/
theorem cutCrossingFaces_length_le_area (extent time : Nat)
    (selected : List Z4Link)
    (hbelow : ∀ link, link ∈ boundaryCompleteSlabLinks extent →
      link.1.2.2.2 < time → link ∈ selected)
    (habove : ∀ link, link ∈ boundaryCompleteSlabLinks extent →
      time < link.1.2.2.2 → link ∉ selected) :
    (cutCrossingFaces extent selected).length ≤ 12 * (extent + 1) ^ 3 := by
  let width := extent + 1
  let candidates := sliceCandidates width time ++ sliceCandidates width (time - 1)
  have hnodup : (cutCrossingFaces extent selected).Nodup :=
    List.filter_sublist.nodup (boundaryCompleteSlabPlaquettes_nodup extent)
  have hsubset : ∀ face, face ∈ cutCrossingFaces extent selected → face ∈ candidates := by
    intro face hface
    have htime := cutCrossingFaces_time_locality extent time selected hbelow habove hface
    have hphysical := (mem_cutCrossingFaces_iff extent selected face).mp hface |>.1
    have hbox := (mem_boundaryCompleteSlabPlaquettes extent face).mp hphysical |>.1
    have hcoords : face.1.1 < width ∧ face.1.2.1 < width ∧
        face.1.2.2.1 < width := by
      have h := (mem_boxPlaquettes face width).mp hbox
      exact ⟨h.1, h.2.1, h.2.2.1⟩
    have hsplit : face.1.2.2.2 = time ∨ face.1.2.2.2 = time - 1 := by omega
    rcases hsplit with ht | ht
    · exact List.mem_append.mpr (Or.inl (face_mem_sliceCandidates hcoords ht))
    · exact List.mem_append.mpr (Or.inr (face_mem_sliceCandidates hcoords ht))
  have hcount := CayleyPruferInjection.nodup_subset_length_le
    (cutCrossingFaces extent selected) candidates hnodup hsubset
  have hcand : candidates.length = 12 * width ^ 3 := by
    simp only [candidates, List.length_append, sliceCandidates_length]
    omega
  rw [hcand] at hcount
  exact hcount

/-- The face-ID mask and the physical crossing-face filter count the same
literal original plaquettes; no duplicate face occurrence is introduced. -/
theorem crossingMask_length_pin (extent : Nat) (selected : List Z4Link) :
    ((slabPhysicalFaceEdges extent).filter
      (crossingMask extent selected)).length =
      (cutCrossingFaces extent selected).length := by
  let pred := fun face : Z4Plaq => cutCrossingFace selected face
  have h := congrArg (fun faces => (faces.filter pred).length) (slabFaceIds_map extent)
  change (((slabPhysicalFaceEdges extent).map (slabPlaquetteAt extent)).filter pred).length =
    (cutCrossingFaces extent selected).length at h
  rw [List.filter_map, List.length_map] at h
  exact h

#print axioms sliceCandidates
#print axioms sliceCandidates_length
#print axioms cutCrossingFaces_length_le_area
#print axioms crossingMask_length_pin

end YMGap.Continuum.BF4ExactSlabReplicaCutArea
