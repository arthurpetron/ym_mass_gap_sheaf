/-
# Geometric time embeddings of the ORIGINAL boundary-complete slabs

The numerical face map is constructed by searching the actual target face
list. Its physicality, injectivity, composition and reflection laws are
proved from the lattice coordinates, without enumerating a slab.

Going from half-size h to h+n increases the extent by 2*n. Translating
coordinates by n preserves distance from the reflection plane; translating
by zero moves a lower observable n steps away from that plane. More
generally a lower shift s<=n is reflected to the upper shift 2*n-s.
These are different embeddings, not endomorphisms of one finite slab.
The repository's slab family also increases its spatial cutoff. No equality
of measures, norm comparison, stationary vacuum or transfer is asserted.
-/

import YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

namespace YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

theorem shift_zero (p : Z4Plaq) : timeShiftPlaquette 0 p = p := by
  obtain ⟨⟨a, b, c, t⟩, plane⟩ := p
  rfl

theorem shift_comp (s t : Nat) (p : Z4Plaq) :
    timeShiftPlaquette t (timeShiftPlaquette s p) = timeShiftPlaquette (s+t) p := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := p
  simp only [timeShiftPlaquette, timeShiftVertex, Nat.add_assoc]

theorem shift_injective (s : Nat) {p q : Z4Plaq}
    (h : timeShiftPlaquette s p = timeShiftPlaquette s q) : p = q := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := p
  obtain ⟨⟨a', b', c', d'⟩, plane'⟩ := q
  simpa only [timeShiftPlaquette, timeShiftVertex, Prod.mk.injEq, Nat.add_right_cancel_iff] using h

theorem shift_face_mem {source target s : Nat} (hs : source+s ≤ target)
    {p : Z4Plaq} (hp : p ∈ boundaryCompleteSlabPlaquettes source) :
    timeShiftPlaquette s p ∈ boundaryCompleteSlabPlaquettes target := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := p
  obtain ⟨hbox, htime⟩ := (mem_boundaryCompleteSlabPlaquettes _ _).mp hp
  rw [mem_boxPlaquettes] at hbox
  change a < source+1 ∧ b < source+1 ∧ c < source+1 ∧ d < source+1 at hbox
  apply (mem_boundaryCompleteSlabPlaquettes _ _).mpr
  have hd : d ≤ source := by
    cases plane <;> simp only [plaquetteTimeAdmissible] at htime <;> omega
  constructor
  · rw [mem_boxPlaquettes]
    change a < target+1 ∧ b < target+1 ∧ c < target+1 ∧ d+s < target+1
    exact ⟨by omega, by omega, by omega, by omega⟩
  · cases plane <;>
      simp only [timeShiftPlaquette, timeShiftVertex, plaquetteTimeAdmissible] at htime ⊢ <;> omega

theorem shift_link_mem {source target s : Nat} (hs : source+s ≤ target)
    {link : Z4Link} (hl : link ∈ boundaryCompleteSlabLinks source) :
    timeShiftLink s link ∈ boundaryCompleteSlabLinks target := by
  obtain ⟨p, hp, hlink⟩ := (mem_boundaryCompleteSlabLinks_iff _ _).mp hl
  refine (mem_boundaryCompleteSlabLinks_iff _ _).mpr ⟨timeShiftPlaquette s p, shift_face_mem hs hp, ?_⟩
  rw [edgesOf_timeShiftPlaquette]
  exact List.mem_map.mpr ⟨link, hlink, rfl⟩

/-- A computable target ID, never an assumed face recoding. -/
def faceId (source target s id : Nat) : Nat :=
  listIndexOf (timeShiftPlaquette s (slabPlaquetteAt source id)) (boundaryCompleteSlabPlaquettes target)

theorem faceId_physical {source target s id : Nat} (hs : source+s ≤ target)
    (hi : id ∈ slabPhysicalFaceEdges source) :
    faceId source target s id ∈ slabPhysicalFaceEdges target :=
  List.mem_range.mpr (listIndexOf_lt_of_mem _ _ (shift_face_mem hs (slabPlaquetteAt_mem hi)))

theorem faceId_pin {source target s id : Nat} (hs : source+s ≤ target)
    (hi : id ∈ slabPhysicalFaceEdges source) :
    slabPlaquetteAt target (faceId source target s id) = timeShiftPlaquette s (slabPlaquetteAt source id) :=
  getD_listIndexOf_of_mem _ _ _ (shift_face_mem hs (slabPlaquetteAt_mem hi))

theorem faceId_injective {source target s i j : Nat} (hs : source+s ≤ target)
    (hi : i ∈ slabPhysicalFaceEdges source) (hj : j ∈ slabPhysicalFaceEdges source)
    (h : faceId source target s i = faceId source target s j) : i = j := by
  apply slabPlaquetteAt_injective_on_physical hi hj
  apply shift_injective s
  rw [← faceId_pin hs hi, ← faceId_pin hs hj, h]

theorem faceId_zero {source id : Nat} (hi : id ∈ slabPhysicalFaceEdges source) :
    faceId source source 0 id = id := by
  apply slabPlaquetteAt_injective_on_physical (faceId_physical (Nat.le_refl source) hi) hi
  rw [faceId_pin (Nat.le_refl source) hi, shift_zero]

theorem faceId_comp {source middle target s t id : Nat}
    (hs : source+s ≤ middle) (ht : middle+t ≤ target) (hi : id ∈ slabPhysicalFaceEdges source) :
    faceId middle target t (faceId source middle s id) = faceId source target (s+t) id := by
  have hst : source+(s+t) ≤ target := by omega
  apply slabPlaquetteAt_injective_on_physical
    (faceId_physical ht (faceId_physical hs hi)) (faceId_physical hst hi)
  rw [faceId_pin ht (faceId_physical hs hi), faceId_pin hs hi, faceId_pin hst hi, shift_comp]

theorem lower_shift {half n s : Nat} (hs : s ≤ n) {p : Z4Plaq}
    (hp : plaquetteHalfSide half p = .lower) :
    plaquetteHalfSide (half+n) (timeShiftPlaquette s p) = .lower := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := p
  cases plane <;>
    simp only [timeShiftPlaquette, timeShiftVertex, plaquetteHalfSide,
      spatialHalfSide, temporalHalfSide] at hp ⊢
  all_goals
    split at hp
    · rw [if_pos (by omega)]
    · first | contradiction | (split at hp <;> contradiction)

theorem central_room {half n s : Nat} (hs : s ≤ n+n) :
    centralExtent half+s ≤ centralExtent (half+n) := by
  unfold centralExtent
  omega

theorem faceId_lower {half n s id : Nat} (hs : s ≤ n)
    (hi : id ∈ centralLowerFaceIds half) :
    faceId (centralExtent half) (centralExtent (half+n)) s id ∈ centralLowerFaceIds (half+n) := by
  have hp := (mem_centralLowerFaceIds.mp hi).1
  have hr := central_room (half := half) (show s ≤ n+n by omega)
  apply mem_centralLowerFaceIds.mpr
  refine ⟨faceId_physical hr hp, ?_⟩
  rw [faceId_pin hr hp]
  exact lower_shift hs (mem_centralLowerFaceIds.mp hi).2

/-- Reflection sends a lower-coordinate shift s to the complementary shift
2*n-s on the reflected face. No cell orientation is dropped. -/
theorem reflection_shift {half n s : Nat} (hs : s ≤ n+n) {p : Z4Plaq}
    (hp : plaquetteTimeAdmissible (centralExtent half) p) :
    timeReflectPlaquette (centralExtent (half+n)) (timeShiftPlaquette s p) =
      timeShiftPlaquette (n+n-s) (timeReflectPlaquette (centralExtent half) p) := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := p
  cases plane <;>
    simp [timeReflectPlaquette, timeShiftPlaquette, timeShiftVertex, centralExtent,
      plaquetteTimeAdmissible] at hp ⊢ <;> omega

theorem faceId_reflection {half n s id : Nat} (hs : s ≤ n+n)
    (hi : id ∈ slabPhysicalFaceEdges (centralExtent half)) :
    slabFaceReflectId (centralExtent (half+n)) (faceId (centralExtent half) (centralExtent (half+n)) s id) =
      faceId (centralExtent half) (centralExtent (half+n)) (n+n-s) (slabFaceReflectId (centralExtent half) id) := by
  have hr := central_room (half := half) hs
  have hc := central_room (half := half) (Nat.sub_le (n+n) s)
  apply slabPlaquetteAt_injective_on_physical
    (slabFaceReflectId_physical (faceId_physical hr hi))
    (faceId_physical hc (slabFaceReflectId_physical hi))
  rw [slabPlaquetteAt_slabFaceReflectId (faceId_physical hr hi), faceId_pin hr hi,
    faceId_pin hc (slabFaceReflectId_physical hi), slabPlaquetteAt_slabFaceReflectId hi]
  exact reflection_shift hs ((mem_boundaryCompleteSlabPlaquettes _ _).mp (slabPlaquetteAt_mem hi)).2

theorem lower_time_le {half : Nat} {p : Z4Plaq} (hp : plaquetteHalfSide half p = .lower) :
    p.1.2.2.2 ≤ half := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := p
  change d ≤ half
  cases plane <;> simp only [plaquetteHalfSide, spatialHalfSide, temporalHalfSide] at hp
  all_goals
    split at hp
    · omega
    · first | contradiction | (split at hp <;> contradiction)

theorem reflected_lower_time_ge {half : Nat} {p : Z4Plaq} (hp : plaquetteHalfSide half p = .lower) :
    half+1 ≤ (timeReflectPlaquette (centralExtent half) p).1.2.2.2 := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := p
  cases plane <;>
    simp only [plaquetteHalfSide, spatialHalfSide, temporalHalfSide] at hp <;>
    simp only [timeReflectPlaquette, centralExtent]
  all_goals
    split at hp
    · omega
    · first | contradiction | (split at hp <;> contradiction)

/-- With independent padding and two outward lags, the reflected time
separation increases by their SUM. This is a coordinate theorem, not a
claim that finite-slab correlations depend only on that sum. -/
theorem reflected_time_separation {half padding s t : Nat}
    (hs : s ≤ padding) (ht : t ≤ padding) {p q : Z4Plaq}
    (hp : plaquetteHalfSide half p = .lower) (hq : plaquetteHalfSide half q = .lower)
    (hphysical : p ∈ boundaryCompleteSlabPlaquettes (centralExtent half)) :
    (timeReflectPlaquette (centralExtent (half+padding)) (timeShiftPlaquette (padding-s) p)).1.2.2.2 -
        (timeShiftPlaquette (padding-t) q).1.2.2.2 =
      (timeReflectPlaquette (centralExtent half) p).1.2.2.2 - q.1.2.2.2 + s+t := by
  rw [reflection_shift (show padding-s ≤ padding+padding by omega)
    ((mem_boundaryCompleteSlabPlaquettes _ _).mp hphysical).2]
  have hleft := reflected_lower_time_ge hp
  have hright := lower_time_le hq
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := q
  generalize timeReflectPlaquette (centralExtent half) p = r at *
  obtain ⟨⟨a', b', c', d'⟩, plane'⟩ := r
  change half+1 ≤ d' at hleft
  change d ≤ half at hright
  change d'+(padding+padding-(padding-s)) - (d+(padding-t)) = d'-d+s+t
  omega

end YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry

#print axioms YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry.shift_zero
#print axioms YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry.shift_comp
#print axioms YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry.shift_injective
#print axioms YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry.shift_face_mem
#print axioms YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry.shift_link_mem
#print axioms YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry.faceId
#print axioms YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry.faceId_physical
#print axioms YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry.faceId_pin
#print axioms YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry.faceId_injective
#print axioms YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry.faceId_zero
#print axioms YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry.faceId_comp
#print axioms YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry.lower_shift
#print axioms YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry.central_room
#print axioms YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry.faceId_lower
#print axioms YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry.reflection_shift
#print axioms YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry.faceId_reflection
#print axioms YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry.lower_time_le
#print axioms YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry.reflected_lower_time_ge
#print axioms YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry.reflected_time_separation
