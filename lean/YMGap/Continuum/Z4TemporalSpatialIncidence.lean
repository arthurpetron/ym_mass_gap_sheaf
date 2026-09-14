/-
# Spatial-link incidence between adjacent temporal cuts

For a temporal-only face list, a spatial link can occur only as the
lower edge of the face above or the upper edge of the face below.
The exact incidence is therefore the sum of two cut occurrence counts.
Distinct faces make each count zero or one. No Haar input is used.
-/

import YMGap.Continuum.Z4ThreeCutSaturation

namespace YMGap.Continuum.Z4TemporalSpatialIncidence

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TemporalCutParityMinimum
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry
open YMGap.Continuum.Z4UnitCubeIncidenceParity

def atTime (time : Nat) (link : Z4Link) : Z4Link :=
  ((link.1.1,link.1.2.1,link.1.2.2.1,time),link.2)

def topEdge (face : Z4Plaq) : Z4Link := (addE face.1 .x3,(dirsOf face.2).1)

theorem bottom_ne_top (face : Z4Plaq) : cutEdge face ≠ topEdge face := by
  rcases face with ⟨⟨a,b,c,t⟩,p⟩
  intro h
  have ht := congrArg (fun l : Z4Link => l.1.2.2.2) h
  simp only [cutEdge, topEdge, addE] at ht
  omega

theorem face_spatial_pin (link : Z4Link) (hd : link.2 ≠ .x3) (face : Z4Plaq)
    (hf : (dirsOf face.2).2 = .x3) :
    (if link ∈ edgesOf face then 1 else 0) =
      (if cutEdge face = link then 1 else 0) + (if topEdge face = link then 1 else 0) := by
  have hm : link ∈ edgesOf face ↔ cutEdge face = link ∨ topEdge face = link := by
    rcases face with ⟨v,p⟩
    rcases link with ⟨u,d⟩
    cases p <;> cases d <;> simp_all [edgesOf, dirsOf, cutEdge, topEdge, eq_comm]
  by_cases h0 : cutEdge face = link
  · have h1 : topEdge face ≠ link := fun h => bottom_ne_top face (h0.trans h.symm)
    have hh := hm.mpr (Or.inl h0)
    simp only [if_pos hh, if_pos h0, if_neg h1, Nat.add_zero]
  · by_cases h1 : topEdge face = link
    · have hh := hm.mpr (Or.inr h1)
      simp only [if_pos hh, if_neg h0, if_pos h1, Nat.zero_add]
    · have hh : link ∉ edgesOf face := fun h => (hm.mp h).elim h0 h1
      simp only [if_neg hh, if_neg h0, if_neg h1, Nat.zero_add]

theorem incidence_sum (link : Z4Link) (hd : link.2 ≠ .x3) : ∀ faces : List Z4Plaq,
    (∀ f, f ∈ faces → (dirsOf f.2).2 = .x3) →
    faceIncidenceCount link faces = occurrenceCount link (faces.map cutEdge) +
      occurrenceCount link (faces.map topEdge)
  | [], _ => rfl
  | f::fs, hp => by
    have ih := incidence_sum link hd fs (fun g hg => hp g (List.mem_cons_of_mem f hg))
    simp only [faceIncidenceCount, List.map_cons, occurrenceCount]
    rw [face_spatial_pin link hd f (hp f List.mem_cons_self)]
    omega

theorem top_at_next (time : Nat) (link : Z4Link) (face : Z4Plaq) :
    topEdge face = atTime (time+1) link ↔ cutEdge face = atTime time link := by
  rcases face with ⟨⟨a,b,c,t⟩,p⟩
  simp only [topEdge, atTime, cutEdge, addE, Prod.mk.injEq, Nat.add_right_cancel_iff]

theorem top_at_zero (link : Z4Link) (face : Z4Plaq) : topEdge face ≠ atTime 0 link := by
  intro h
  have ht := congrArg (fun l : Z4Link => l.1.2.2.2) h
  simp only [topEdge, atTime, addE] at ht
  omega

theorem top_count_next (time : Nat) (link : Z4Link) : ∀ faces : List Z4Plaq,
    occurrenceCount (atTime (time+1) link) (faces.map topEdge) =
      occurrenceCount (atTime time link) (faces.map cutEdge)
  | [] => rfl
  | f::fs => by
    simp only [List.map_cons, occurrenceCount, top_at_next, top_count_next time link fs]

theorem top_count_zero (link : Z4Link) : ∀ faces : List Z4Plaq,
    occurrenceCount (atTime 0 link) (faces.map topEdge) = 0
  | [] => rfl
  | f::fs => by
    simp only [List.map_cons, occurrenceCount, if_neg (top_at_zero link f), Nat.zero_add,
      top_count_zero link fs]

theorem bottom_on_cut (time : Nat) (link : Z4Link) : ∀ faces : List Z4Plaq,
    (∀ f, f ∈ faces → (dirsOf f.2).2 = .x3) →
    occurrenceCount (atTime time link) (faces.map cutEdge) =
      occurrenceCount (atTime time link) (cut time faces)
  | [], _ => rfl
  | f::fs, hp => by
    have ih := bottom_on_cut time link fs (fun g hg => hp g (List.mem_cons_of_mem f hg))
    cases hc : crosses time f with
    | true =>
      simp only [cut, List.filter_cons, hc, ↓reduceIte, List.map_cons, occurrenceCount] at ih ⊢
      rw [ih]
    | false =>
      have hn : cutEdge f ≠ atTime time link := by
        intro he
        have ht := congrArg (fun l : Z4Link => l.1.2.2.2) he
        have hh : crosses time f = true := decide_eq_true ⟨hp f List.mem_cons_self,ht⟩
        rw [hc] at hh
        cases hh
      simp only [cut, List.filter_cons, hc, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, occurrenceCount, if_neg hn, Nat.zero_add] at ih ⊢
      exact ih

def cutCount (time : Nat) (link : Z4Link) (faces : List Z4Plaq) : Nat :=
  occurrenceCount (atTime time link) (cut time faces)

theorem cutCount_le_one (time : Nat) (link : Z4Link) (faces : List Z4Plaq) (hn : faces.Nodup) :
    cutCount time link faces ≤ 1 := by
  by_cases hm : atTime time link ∈ cut time faces
  · rw [cutCount, occurrenceCount_eq_one_of_mem_nodup _ _ (cut_nodup time faces hn) hm]
    exact Nat.le_refl 1
  · rw [cutCount, occurrenceCount_eq_zero_of_not_mem _ _ hm]
    exact Nat.zero_le _

theorem spatial_next (time : Nat) (link : Z4Link) (hd : link.2 ≠ .x3) (faces : List Z4Plaq)
    (hp : ∀ f, f ∈ faces → (dirsOf f.2).2 = .x3) :
    faceIncidenceCount (atTime (time+1) link) faces = cutCount (time+1) link faces + cutCount time link faces := by
  rw [incidence_sum (atTime (time+1) link) hd faces hp, top_count_next,
    bottom_on_cut _ _ faces hp, bottom_on_cut _ _ faces hp]
  rfl

theorem spatial_zero (link : Z4Link) (hd : link.2 ≠ .x3) (faces : List Z4Plaq)
    (hp : ∀ f, f ∈ faces → (dirsOf f.2).2 = .x3) :
    faceIncidenceCount (atTime 0 link) faces = cutCount 0 link faces := by
  rw [incidence_sum (atTime 0 link) hd faces hp, top_count_zero, Nat.add_zero, bottom_on_cut _ _ faces hp]
  rfl

end YMGap.Continuum.Z4TemporalSpatialIncidence

#print axioms YMGap.Continuum.Z4TemporalSpatialIncidence.atTime
#print axioms YMGap.Continuum.Z4TemporalSpatialIncidence.topEdge
#print axioms YMGap.Continuum.Z4TemporalSpatialIncidence.bottom_ne_top
#print axioms YMGap.Continuum.Z4TemporalSpatialIncidence.face_spatial_pin
#print axioms YMGap.Continuum.Z4TemporalSpatialIncidence.incidence_sum
#print axioms YMGap.Continuum.Z4TemporalSpatialIncidence.top_at_next
#print axioms YMGap.Continuum.Z4TemporalSpatialIncidence.top_at_zero
#print axioms YMGap.Continuum.Z4TemporalSpatialIncidence.top_count_next
#print axioms YMGap.Continuum.Z4TemporalSpatialIncidence.top_count_zero
#print axioms YMGap.Continuum.Z4TemporalSpatialIncidence.bottom_on_cut
#print axioms YMGap.Continuum.Z4TemporalSpatialIncidence.cutCount
#print axioms YMGap.Continuum.Z4TemporalSpatialIncidence.cutCount_le_one
#print axioms YMGap.Continuum.Z4TemporalSpatialIncidence.spatial_next
#print axioms YMGap.Continuum.Z4TemporalSpatialIncidence.spatial_zero
