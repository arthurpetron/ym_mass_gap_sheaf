/-
# Spatial defects determine temporal parity

For a distinct finite face list, the spatial-link charge equation is a
binary recurrence in time. Its source is the prescribed endpoint charge
plus incidence from spatial faces. The decoder below computes every
temporal cut bit from those sources, starting at the lattice boundary.
No temporal-window, spin cutoff, connectedness or weight estimate is used.
-/

import YMGap.Continuum.Z4TemporalSpatialIncidence

namespace YMGap.Continuum.Z4SpatialDefectTemporalDecoder

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4TemporalSpatialIncidence
open YMGap.Continuum.Z4TemporalCutParityMinimum
open YMGap.Continuum.Z4UnitCubeIncidenceParity

def temporalFaces (faces : List Z4Plaq) : List Z4Plaq :=
  faces.filter (fun f => decide ((dirsOf f.2).2 = Dir4.x3))

def spatialFaces (faces : List Z4Plaq) : List Z4Plaq :=
  faces.filter (fun f => decide ((dirsOf f.2).2 ≠ Dir4.x3))

theorem temporalFaces_temporal (faces : List Z4Plaq) (f : Z4Plaq)
    (hf : f ∈ temporalFaces faces) : (dirsOf f.2).2 = Dir4.x3 :=
  of_decide_eq_true (List.mem_filter.mp hf).2

theorem incidence_split (link : Z4Link) : ∀ faces : List Z4Plaq,
    faceIncidenceCount link faces = faceIncidenceCount link (spatialFaces faces) +
      faceIncidenceCount link (temporalFaces faces)
  | [] => rfl
  | f :: fs => by
    have ih := incidence_split link fs
    by_cases ht : (dirsOf f.2).2 = Dir4.x3
    · simp only [spatialFaces, temporalFaces, List.filter_cons, ne_eq, ht, not_true_eq_false,
        decide_true, decide_false, Bool.false_eq_true, ↓reduceIte, faceIncidenceCount] at ih ⊢
      omega
    · simp only [spatialFaces, temporalFaces, List.filter_cons, ne_eq, ht, not_false_eq_true,
        decide_true, decide_false, Bool.false_eq_true, ↓reduceIte, faceIncidenceCount] at ih ⊢
      omega

theorem cut_temporalFaces (time : Nat) : ∀ faces : List Z4Plaq,
    cut time (temporalFaces faces) = cut time faces
  | [] => rfl
  | f :: fs => by
    have ih := cut_temporalFaces time fs
    by_cases ht : (dirsOf f.2).2 = Dir4.x3
    · cases hx : crosses time f <;>
        simpa only [temporalFaces, List.filter_cons, ht, decide_true, ↓reduceIte,
          cut, hx, Bool.false_eq_true, List.map_cons] using congrArg
            (fun xs => if crosses time f then cutEdge f :: xs else xs) ih
    · have hx : crosses time f = false := by simp only [crosses, ht, false_and, decide_false]
      simpa only [temporalFaces, List.filter_cons, ht, decide_false, Bool.false_eq_true,
        ↓reduceIte, cut, hx] using ih

theorem cutCount_temporalFaces (time : Nat) (link : Z4Link) (faces : List Z4Plaq) :
    cutCount time link (temporalFaces faces) = cutCount time link faces := by
  rw [cutCount, cut_temporalFaces]
  rfl

theorem incidence_zero (link : Z4Link) (hd : link.2 ≠ .x3) (faces : List Z4Plaq) :
    faceIncidenceCount (atTime 0 link) faces =
      faceIncidenceCount (atTime 0 link) (spatialFaces faces) + cutCount 0 link faces := by
  rw [incidence_split, spatial_zero link hd _ (temporalFaces_temporal faces),
    cutCount_temporalFaces]

theorem incidence_next (time : Nat) (link : Z4Link) (hd : link.2 ≠ .x3)
    (faces : List Z4Plaq) :
    faceIncidenceCount (atTime (time+1) link) faces =
      faceIncidenceCount (atTime (time+1) link) (spatialFaces faces) +
        (cutCount (time+1) link faces + cutCount time link faces) := by
  rw [incidence_split, spatial_next time link hd _ (temporalFaces_temporal faces),
    cutCount_temporalFaces, cutCount_temporalFaces]

/-- An explicit decoder; no witness is extracted from a proposition. -/
def temporalBit (charge spatial : Nat → Nat) : Nat → Nat
  | 0 => (charge 0 + spatial 0) % 2
  | time+1 => (charge (time+1) + spatial (time+1) + temporalBit charge spatial time) % 2

theorem temporalBit_le_one (charge spatial : Nat → Nat) (time : Nat) :
    temporalBit charge spatial time ≤ 1 := by
  cases time <;> simp only [temporalBit] <;> omega

theorem cutCount_decode (charge : Nat → Nat) (link : Z4Link) (hd : link.2 ≠ .x3)
    (faces : List Z4Plaq) (hn : faces.Nodup)
    (hp : ∀ time, (charge time + faceIncidenceCount (atTime time link) faces) % 2 = 0) :
    ∀ time, cutCount time link faces = temporalBit charge
      (fun t => faceIncidenceCount (atTime t link) (spatialFaces faces)) time
  | 0 => by
    have h := hp 0
    rw [incidence_zero link hd faces] at h
    have hb := cutCount_le_one 0 link faces hn
    simp only [temporalBit]
    omega
  | time+1 => by
    have h := hp (time+1)
    rw [incidence_next time link hd faces] at h
    have hb := cutCount_le_one (time+1) link faces hn
    have ih := cutCount_decode charge link hd faces hn hp time
    simp only [temporalBit]
    omega

theorem same_spatial_same_cuts (charge : Nat → Nat) (link : Z4Link) (hd : link.2 ≠ .x3)
    (left right : List Z4Plaq) (hl : left.Nodup) (hr : right.Nodup)
    (hleft : ∀ time, (charge time + faceIncidenceCount (atTime time link) left) % 2 = 0)
    (hright : ∀ time, (charge time + faceIncidenceCount (atTime time link) right) % 2 = 0)
    (hs : spatialFaces left = spatialFaces right) (time : Nat) :
    cutCount time link left = cutCount time link right := by
  rw [cutCount_decode charge link hd left hl hleft,
    cutCount_decode charge link hd right hr hright, hs]

end YMGap.Continuum.Z4SpatialDefectTemporalDecoder

#print axioms YMGap.Continuum.Z4SpatialDefectTemporalDecoder.temporalFaces
#print axioms YMGap.Continuum.Z4SpatialDefectTemporalDecoder.spatialFaces
#print axioms YMGap.Continuum.Z4SpatialDefectTemporalDecoder.temporalFaces_temporal
#print axioms YMGap.Continuum.Z4SpatialDefectTemporalDecoder.incidence_split
#print axioms YMGap.Continuum.Z4SpatialDefectTemporalDecoder.cut_temporalFaces
#print axioms YMGap.Continuum.Z4SpatialDefectTemporalDecoder.cutCount_temporalFaces
#print axioms YMGap.Continuum.Z4SpatialDefectTemporalDecoder.incidence_zero
#print axioms YMGap.Continuum.Z4SpatialDefectTemporalDecoder.incidence_next
#print axioms YMGap.Continuum.Z4SpatialDefectTemporalDecoder.temporalBit
#print axioms YMGap.Continuum.Z4SpatialDefectTemporalDecoder.temporalBit_le_one
#print axioms YMGap.Continuum.Z4SpatialDefectTemporalDecoder.cutCount_decode
#print axioms YMGap.Continuum.Z4SpatialDefectTemporalDecoder.same_spatial_same_cuts
