/-
# Finite temporal conservation leaves the projected spatial boundary

An explicit prefix of spatial impulses augments the endpoint decoder.
Above the finite face-time ceiling, the temporal cut is empty and the
prefix contains every spatial face. Thus the projected spatial boundary
has precisely the total endpoint parity, for arbitrary finite surfaces.
No gauge, spin, weight, cutoff or prescribed spatial-face count is used.
-/

import YMGap.Continuum.Z4TwoSpatialFaceContinuation

namespace YMGap.Continuum.Z4FiniteProjectedBoundaryParity

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TemporalSpatialIncidence
open YMGap.Continuum.Z4TemporalCutParityMinimum
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4SpatialDefectTemporalDecoder
open YMGap.Continuum.Z4FiniteTemporalEndpointParity
open YMGap.Continuum.Z4FiniteTemporalSpatialSources
open YMGap.Continuum.Z4SpatialPlaquetteProjection
open YMGap.Continuum.Z4TwoSpatialFaceContinuation

def spatialPrefix (link : Z4Link) (time : Nat) : List Z4Plaq → Nat
  | [] => 0
  | face::faces => (if face.1.2.2.2 ≤ time then projectedBit face link else 0)+
      spatialPrefix link time faces

def projectedCount (link : Z4Link) : List Z4Plaq → Nat
  | [] => 0
  | face::faces => projectedBit face link+projectedCount link faces

theorem spatialPrefix_zero (link : Z4Link) : ∀ faces : List Z4Plaq,
    (∀ face, face ∈ faces → (dirsOf face.2).2 ≠ Dir4.x3) →
    spatialPrefix link 0 faces=faceIncidenceCount (atTime 0 link) faces
  | [], _ => rfl
  | face::faces, hs => by
    rw [spatialPrefix,faceIncidenceCount,spatial_indicator_impulse 0 link face
      (hs face List.mem_cons_self),spatialPrefix_zero link faces
        (fun f hf => hs f (List.mem_cons_of_mem face hf))]
    simp only [projectedBit,Nat.le_zero_eq,eq_comm]

theorem spatialPrefix_next (link : Z4Link) (time : Nat) : ∀ faces : List Z4Plaq,
    (∀ face, face ∈ faces → (dirsOf face.2).2 ≠ Dir4.x3) →
    spatialPrefix link (time+1) faces=
      faceIncidenceCount (atTime (time+1) link) faces+spatialPrefix link time faces
  | [], _ => rfl
  | face::faces, hs => by
    have ih := spatialPrefix_next link time faces (fun f hf => hs f (List.mem_cons_of_mem face hf))
    have hi := impulse_step face.1.2.2.2 (projectedBit face link) time
    simp only [spatialPrefix,faceIncidenceCount]
    rw [spatial_indicator_impulse (time+1) link face (hs face List.mem_cons_self)]
    change (if face.1.2.2.2 ≤ time+1 then projectedBit face link else 0)+_=
      ((if time+1=face.1.2.2.2 then projectedBit face link else 0)+_)+_
    omega

theorem spatialPrefix_full (link : Z4Link) (time : Nat) : ∀ faces : List Z4Plaq,
    (∀ face, face ∈ faces → face.1.2.2.2 ≤ time) →
    spatialPrefix link time faces=projectedCount link faces
  | [], _ => rfl
  | face::faces, hs => by
    rw [spatialPrefix,projectedCount,if_pos (hs face List.mem_cons_self),
      spatialPrefix_full link time faces (fun f hf => hs f (List.mem_cons_of_mem face hf))]

theorem face_time_le_ceiling : ∀ faces : List Z4Plaq, ∀ face,
    face ∈ faces → face.1.2.2.2 ≤ timeCeiling faces
  | f::fs, face, hm => by
    have hl := Nat.le_max_left (f.1.2.2.2+1) (timeCeiling fs)
    have hr := Nat.le_max_right (f.1.2.2.2+1) (timeCeiling fs)
    rcases List.mem_cons.mp hm with rfl | hm
    · change face.1.2.2.2 ≤ max (face.1.2.2.2+1) (timeCeiling fs)
      omega
    · exact Nat.le_trans (face_time_le_ceiling fs face hm) hr

theorem endpoint_spatial_decode (lower upper a b : Nat) (link : Z4Link)
    (faces : List Z4Plaq) (hs : ∀ face, face ∈ faces → (dirsOf face.2).2 ≠ Dir4.x3) : ∀ time,
    temporalBit (twoImpulses lower upper a b) (fun t => faceIncidenceCount (atTime t link) faces) time=
      ((if lower ≤ time then a else 0)+(if upper ≤ time then b else 0)+spatialPrefix link time faces)%2
  | 0 => by
    rw [spatialPrefix_zero link faces hs]
    simp only [temporalBit,twoImpulses,Nat.le_zero_eq,eq_comm]
  | time+1 => by
    rw [temporalBit,endpoint_spatial_decode lower upper a b link faces hs time,
      spatialPrefix_next link time faces hs]
    simp only [twoImpulses]
    have hl := impulse_step lower a time
    have hu := impulse_step upper b time
    omega

theorem endpoint_projected_parity (lower upper a b : Nat) (link : Z4Link)
    (hd : link.2 ≠ Dir4.x3) (faces : List Z4Plaq) (hn : faces.Nodup)
    (hp : ∀ time, (twoImpulses lower upper a b time+faceIncidenceCount (atTime time link) faces)%2=0) :
    (a+b+projectedCount link (spatialFaces faces))%2=0 := by
  let time := max (timeCeiling faces) (max lower upper)
  have hc := cutCount_decode (twoImpulses lower upper a b) link hd faces hn hp time
  have hz : cutCount time link faces=0 := by
    rw [cutCount,cut_above_ceiling time faces (Nat.le_max_left _ _)]
    rfl
  have hs : ∀ face, face ∈ spatialFaces faces → (dirsOf face.2).2 ≠ Dir4.x3 :=
    fun _ hf => of_decide_eq_true (List.mem_filter.mp hf).2
  have ht : ∀ face, face ∈ spatialFaces faces → face.1.2.2.2 ≤ time :=
    fun face hf => Nat.le_trans (face_time_le_ceiling faces face (List.mem_filter.mp hf).1) (Nat.le_max_left _ _)
  have hl : lower ≤ time := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hu : upper ≤ time := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  rw [endpoint_spatial_decode lower upper a b link _ hs time,if_pos hl,if_pos hu,
    spatialPrefix_full link time _ ht,hz] at hc
  exact hc.symm

theorem projectedCount_append (link : Z4Link) : ∀ left right : List Z4Plaq,
    projectedCount link (left++right)=projectedCount link left+projectedCount link right
  | [], _ => by simp only [List.nil_append,projectedCount,Nat.zero_add]
  | face::faces, right => by
    simp only [List.cons_append,projectedCount,projectedCount_append link faces right,Nat.add_assoc]

theorem projectedCount_eq_incidence (link : Z4Link) : ∀ faces : List Z4Plaq,
    (∀ face, face ∈ faces → (dirsOf face.2).2 ≠ Dir4.x3) →
    projectedCount link faces=faceIncidenceCount (atTime 0 link) (faces.map (faceAt 0))
  | [], _ => rfl
  | face::faces, hs => by
    rw [projectedCount,List.map_cons,faceIncidenceCount,projectedCount_eq_incidence link faces
      (fun f hf => hs f (List.mem_cons_of_mem face hf))]
    have he := retimed_spatial_boundary_mem 0 face (hs face List.mem_cons_self) link
    by_cases hm : atTime face.1.2.2.2 link ∈ edgesOf face
    · rw [projectedBit,if_pos hm,if_pos (he.mpr hm)]
    · rw [projectedBit,if_neg hm,if_neg (fun h => hm (he.mp h))]

end YMGap.Continuum.Z4FiniteProjectedBoundaryParity

#print axioms YMGap.Continuum.Z4FiniteProjectedBoundaryParity.spatialPrefix
#print axioms YMGap.Continuum.Z4FiniteProjectedBoundaryParity.projectedCount
#print axioms YMGap.Continuum.Z4FiniteProjectedBoundaryParity.spatialPrefix_zero
#print axioms YMGap.Continuum.Z4FiniteProjectedBoundaryParity.spatialPrefix_next
#print axioms YMGap.Continuum.Z4FiniteProjectedBoundaryParity.spatialPrefix_full
#print axioms YMGap.Continuum.Z4FiniteProjectedBoundaryParity.face_time_le_ceiling
#print axioms YMGap.Continuum.Z4FiniteProjectedBoundaryParity.endpoint_spatial_decode
#print axioms YMGap.Continuum.Z4FiniteProjectedBoundaryParity.endpoint_projected_parity
#print axioms YMGap.Continuum.Z4FiniteProjectedBoundaryParity.projectedCount_append
#print axioms YMGap.Continuum.Z4FiniteProjectedBoundaryParity.projectedCount_eq_incidence
