/-
# A single spatial cap has the endpoint's projected boundary

The finite temporal decoder conserves the sum of endpoint and spatial
sources. If a finite odd-face surface has one spatial face and one
spatial endpoint plaquette, their projected boundary indicators agree.
The cap time is not prescribed. No spin, weight, cutoff or time-window
assumption enters this geometric statement.
-/

import YMGap.Continuum.Z4FiniteTemporalEndpointParity

namespace YMGap.Continuum.Z4FiniteTemporalSpatialSources

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TemporalSpatialIncidence
open YMGap.Continuum.Z4TemporalCutParityMinimum
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4SpatialDefectTemporalDecoder
open YMGap.Continuum.Z4FiniteTemporalEndpointParity

theorem temporalBit_source_congr (charge spatial charge' spatial' : Nat → Nat)
    (hs : ∀ time, charge time + spatial time = charge' time + spatial' time) :
    ∀ time, temporalBit charge spatial time = temporalBit charge' spatial' time
  | 0 => by simp only [temporalBit, hs]
  | time+1 => by rw [temporalBit, temporalBit, hs, temporalBit_source_congr _ _ _ _ hs time]

theorem two_source_sum_even (lower upper a b : Nat) (charge : Nat → Nat)
    (link : Z4Link) (hd : link.2 ≠ Dir4.x3) (faces : List Z4Plaq) (hn : faces.Nodup)
    (hp : ∀ time, (charge time + faceIncidenceCount (atTime time link) faces) % 2 = 0)
    (hs : ∀ time, charge time + faceIncidenceCount (atTime time link) (spatialFaces faces) =
      twoImpulses lower upper a b time) : (a+b) % 2 = 0 := by
  let time := max (timeCeiling faces) (max lower upper)
  have hc := cutCount_decode charge link hd faces hn hp time
  have he := temporalBit_source_congr charge
    (fun t => faceIncidenceCount (atTime t link) (spatialFaces faces))
    (twoImpulses lower upper a b) (fun _ => 0) (fun t => by simpa only [Nat.add_zero] using hs t) time
  have hz : cutCount time link faces = 0 := by
    rw [cutCount, cut_above_ceiling time faces (Nat.le_max_left _ _)]
    rfl
  have hl : lower ≤ time := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hu : upper ≤ time := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  rw [he, two_impulses_decode, if_pos hl, if_pos hu, hz] at hc
  exact hc.symm

theorem spatial_boundary_time (face : Z4Plaq) (hs : (dirsOf face.2).2 ≠ Dir4.x3)
    (link : Z4Link) (hl : link ∈ edgesOf face) : link.1.2.2.2 = face.1.2.2.2 := by
  rcases face with ⟨⟨a,b,c,t⟩,p⟩
  cases p <;> simp only [dirsOf, ne_eq] at hs
  all_goals try exact False.elim (hs True.intro)
  all_goals
    simp only [edgesOf, dirsOf, addE, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with h | h | h | h <;> subst link <;> rfl

theorem retimed_spatial_mem (time : Nat) (link : Z4Link) (face : Z4Plaq)
    (hs : (dirsOf face.2).2 ≠ Dir4.x3) :
    atTime time link ∈ edgesOf face ↔ time = face.1.2.2.2 ∧
      atTime face.1.2.2.2 link ∈ edgesOf face := by
  constructor
  · intro h
    have ht : time = face.1.2.2.2 := spatial_boundary_time face hs (atTime time link) h
    exact ⟨ht,ht ▸ h⟩
  · rintro ⟨ht,h⟩
    exact ht ▸ h

theorem spatial_indicator_impulse (time : Nat) (link : Z4Link) (face : Z4Plaq)
    (hs : (dirsOf face.2).2 ≠ Dir4.x3) :
    (if atTime time link ∈ edgesOf face then 1 else 0) =
      if time = face.1.2.2.2 then (if atTime face.1.2.2.2 link ∈ edgesOf face then 1 else 0) else 0 := by
  by_cases ht : time = face.1.2.2.2
  · subst time
    rw [if_pos rfl]
  · have hn : atTime time link ∉ edgesOf face :=
      fun h => ht ((retimed_spatial_mem time link face hs).mp h).1
    rw [if_neg hn, if_neg ht]

/-- Equality of the two projected boundary indicators follows from the empty
terminal cut, not from an assumed cap position or a prescribed surface. -/
theorem single_spatial_boundary_projection (probe cap : Z4Plaq)
    (hprobe : (dirsOf probe.2).2 ≠ Dir4.x3) (faces : List Z4Plaq) (hn : faces.Nodup)
    (hs : spatialFaces faces = [cap])
    (hp : ∀ link, ((if link ∈ edgesOf probe then 1 else 0) +
      faceIncidenceCount link faces) % 2 = 0)
    (link : Z4Link) (hd : link.2 ≠ Dir4.x3) :
    atTime cap.1.2.2.2 link ∈ edgesOf cap ↔ atTime probe.1.2.2.2 link ∈ edgesOf probe := by
  have hcap : (dirsOf cap.2).2 ≠ Dir4.x3 :=
    of_decide_eq_true (List.mem_filter.mp (show cap ∈ spatialFaces faces from hs ▸ List.mem_cons_self)).2
  let a := if atTime probe.1.2.2.2 link ∈ edgesOf probe then 1 else 0
  let b := if atTime cap.1.2.2.2 link ∈ edgesOf cap then 1 else 0
  have he := two_source_sum_even probe.1.2.2.2 cap.1.2.2.2 a b
    (fun t => if atTime t link ∈ edgesOf probe then 1 else 0) link hd faces hn
    (fun t => hp (atTime t link)) (fun t => by
      rw [hs]
      simp only [faceIncidenceCount, Nat.add_zero, twoImpulses]
      rw [spatial_indicator_impulse t link probe hprobe, spatial_indicator_impulse t link cap hcap])
  by_cases ha : atTime probe.1.2.2.2 link ∈ edgesOf probe <;>
    by_cases hb : atTime cap.1.2.2.2 link ∈ edgesOf cap
  · exact ⟨fun _ => ha,fun _ => hb⟩
  · simp only [a, b, if_pos ha, if_neg hb] at he
    contradiction
  · simp only [a, b, if_neg ha, if_pos hb] at he
    contradiction
  · exact ⟨fun h => False.elim (hb h),fun h => False.elim (ha h)⟩

end YMGap.Continuum.Z4FiniteTemporalSpatialSources

#print axioms YMGap.Continuum.Z4FiniteTemporalSpatialSources.temporalBit_source_congr
#print axioms YMGap.Continuum.Z4FiniteTemporalSpatialSources.two_source_sum_even
#print axioms YMGap.Continuum.Z4FiniteTemporalSpatialSources.spatial_boundary_time
#print axioms YMGap.Continuum.Z4FiniteTemporalSpatialSources.retimed_spatial_mem
#print axioms YMGap.Continuum.Z4FiniteTemporalSpatialSources.spatial_indicator_impulse
#print axioms YMGap.Continuum.Z4FiniteTemporalSpatialSources.single_spatial_boundary_projection
