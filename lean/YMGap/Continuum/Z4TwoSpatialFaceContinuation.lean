/-
# Two spatial faces with equal endpoint charges have equal projections

The exact temporal decoder has four impulses: two equal endpoint charges
and the two spatial-face boundary indicators. The empty terminal cut
forces the latter indicators to agree. This derives the common spatial
projection; it does not assume it, prescribe cap times or bound a weight.
-/

import YMGap.Continuum.Z4SpatialPlaquetteProjection

namespace YMGap.Continuum.Z4TwoSpatialFaceContinuation

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TemporalSpatialIncidence
open YMGap.Continuum.Z4TemporalCutParityMinimum
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4SpatialDefectTemporalDecoder
open YMGap.Continuum.Z4FiniteTemporalEndpointParity
open YMGap.Continuum.Z4FiniteTemporalSpatialSources
open YMGap.Continuum.Z4SpatialPlaquetteProjection

def projectedBit (face : Z4Plaq) (link : Z4Link) : Nat :=
  if atTime face.1.2.2.2 link ∈ edgesOf face then 1 else 0

theorem four_impulses_decode (t0 t1 t2 t3 a b c d : Nat) : ∀ time,
    temporalBit (twoImpulses t0 t1 a b) (twoImpulses t2 t3 c d) time =
      ((if t0 ≤ time then a else 0)+(if t1 ≤ time then b else 0)+
        (if t2 ≤ time then c else 0)+(if t3 ≤ time then d else 0))%2
  | 0 => by
    simp only [temporalBit, twoImpulses, Nat.le_zero_eq, eq_comm]
    omega
  | time+1 => by
    rw [temporalBit, four_impulses_decode t0 t1 t2 t3 a b c d time]
    simp only [twoImpulses]
    have h0 := impulse_step t0 a time
    have h1 := impulse_step t1 b time
    have h2 := impulse_step t2 c time
    have h3 := impulse_step t3 d time
    omega

theorem two_spatial_cut_decode (lower upper q : Nat) (charge : Nat → Nat)
    (link : Z4Link) (hd : link.2 ≠ Dir4.x3) (faces : List Z4Plaq) (hn : faces.Nodup)
    (left right : Z4Plaq) (hs : spatialFaces faces=[left,right])
    (hc : ∀ time, charge time=twoImpulses lower upper q q time)
    (hp : ∀ time, (charge time+faceIncidenceCount (atTime time link) faces)%2=0) (time : Nat) :
    cutCount time link faces =
      ((if lower ≤ time then q else 0)+(if upper ≤ time then q else 0)+
        (if left.1.2.2.2 ≤ time then projectedBit left link else 0)+
        (if right.1.2.2.2 ≤ time then projectedBit right link else 0))%2 := by
  have hl : (dirsOf left.2).2 ≠ Dir4.x3 :=
    of_decide_eq_true (List.mem_filter.mp (show left ∈ spatialFaces faces from hs ▸ List.mem_cons_self)).2
  have hr : (dirsOf right.2).2 ≠ Dir4.x3 :=
    of_decide_eq_true (List.mem_filter.mp (show right ∈ spatialFaces faces from
      hs ▸ List.mem_cons_of_mem _ List.mem_cons_self)).2
  rw [cutCount_decode charge link hd faces hn hp time]
  have he := temporalBit_source_congr charge
    (fun t => faceIncidenceCount (atTime t link) (spatialFaces faces))
    (twoImpulses lower upper q q)
    (twoImpulses left.1.2.2.2 right.1.2.2.2 (projectedBit left link) (projectedBit right link))
    (fun t => by
      rw [hc,hs]
      simp only [faceIncidenceCount, Nat.add_zero, twoImpulses]
      rw [spatial_indicator_impulse t link left hl,spatial_indicator_impulse t link right hr]
      rfl) time
  exact he.trans (four_impulses_decode _ _ _ _ _ _ _ _ time)

theorem two_spatial_projected_boundary (lower upper q : Nat) (charge : Nat → Nat)
    (link : Z4Link) (hd : link.2 ≠ Dir4.x3) (faces : List Z4Plaq) (hn : faces.Nodup)
    (left right : Z4Plaq) (hs : spatialFaces faces=[left,right])
    (hc : ∀ time, charge time=twoImpulses lower upper q q time)
    (hp : ∀ time, (charge time+faceIncidenceCount (atTime time link) faces)%2=0) :
    atTime left.1.2.2.2 link ∈ edgesOf left ↔ atTime right.1.2.2.2 link ∈ edgesOf right := by
  let time := max (timeCeiling faces) (max lower (max upper (max left.1.2.2.2 right.1.2.2.2)))
  have h := two_spatial_cut_decode lower upper q charge link hd faces hn left right hs hc hp time
  have hz : cutCount time link faces=0 := by
    rw [cutCount,cut_above_ceiling time faces (Nat.le_max_left _ _)]
    rfl
  have h0 : lower ≤ time := by dsimp only [time]; omega
  have h1 : upper ≤ time := by dsimp only [time]; omega
  have h2 : left.1.2.2.2 ≤ time := by dsimp only [time]; omega
  have h3 : right.1.2.2.2 ≤ time := by dsimp only [time]; omega
  rw [hz,if_pos h0,if_pos h1,if_pos h2,if_pos h3] at h
  by_cases hl : atTime left.1.2.2.2 link ∈ edgesOf left <;>
    by_cases hr : atTime right.1.2.2.2 link ∈ edgesOf right
  · exact ⟨fun _ => hr,fun _ => hl⟩
  · have hf : False := by simp only [projectedBit,if_pos hl,if_neg hr] at h; omega
    exact False.elim hf
  · have hf : False := by simp only [projectedBit,if_neg hl,if_pos hr] at h; omega
    exact False.elim hf
  · exact ⟨fun hx => False.elim (hl hx),fun hx => False.elim (hr hx)⟩

end YMGap.Continuum.Z4TwoSpatialFaceContinuation

#print axioms YMGap.Continuum.Z4TwoSpatialFaceContinuation.projectedBit
#print axioms YMGap.Continuum.Z4TwoSpatialFaceContinuation.four_impulses_decode
#print axioms YMGap.Continuum.Z4TwoSpatialFaceContinuation.two_spatial_cut_decode
#print axioms YMGap.Continuum.Z4TwoSpatialFaceContinuation.two_spatial_projected_boundary
