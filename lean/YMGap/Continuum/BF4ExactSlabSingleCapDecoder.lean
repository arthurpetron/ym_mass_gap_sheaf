/-
# The original single-cap temporal surface is an interval tube

The original accepted one-endpoint checker and singleton spatial list
determine every temporal cut bit. The cut is occupied exactly between
the endpoint time and the computed cap time. No time-window assumption
or fundamental-spin restriction is used here.
-/

import YMGap.Continuum.BF4ExactSlabSingleSpatialCap

namespace YMGap.Continuum.BF4ExactSlabSingleCapDecoder

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4TemporalSpatialIncidence
open YMGap.Continuum.Z4TemporalCutParityMinimum
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4SpatialDefectTemporalDecoder
open YMGap.Continuum.Z4FiniteTemporalEndpointParity
open YMGap.Continuum.Z4FiniteTemporalSpatialSources
open YMGap.Continuum.BF4ExactSlabOddFaceIncidence
open YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabMinimalMomentParity
open YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction
open YMGap.Continuum.BF4ExactSlabSingleSpatialCap

def endpointTime (margin : Nat) (lo : Bool) : Nat := if lo then margin else margin+3

def boundaryBit (margin : Nat) (link : Z4Link) : Nat :=
  if atTime margin link ∈ edgesOf (sliceFace margin 0) then 1 else 0

theorem cap_boundary_mem (margin time : Nat) (link : Z4Link) :
    atTime time link ∈ edgesOf (capFace margin time) ↔
      atTime margin link ∈ edgesOf (sliceFace margin 0) := by
  rcases link with ⟨⟨a,b,c,t⟩,d⟩
  simp only [atTime, capFace, sliceFace, edgesOf, dirsOf, addE, List.mem_cons,
    List.not_mem_nil, or_false, Prod.mk.injEq, Nat.add_zero, and_true]

theorem cap_indicator (margin time t : Nat) (link : Z4Link) :
    (if atTime t link ∈ edgesOf (capFace margin time) then 1 else 0) =
      if t=time then boundaryBit margin link else 0 := by
  rw [spatial_indicator_impulse t link (capFace margin time) (by change Dir4.x1 ≠ Dir4.x3; decide)]
  change (if t=time then (if atTime time link ∈ edgesOf (capFace margin time) then 1 else 0) else 0) = _
  have hm := cap_boundary_mem margin time link
  by_cases h : atTime margin link ∈ edgesOf (sliceFace margin 0)
  · have hc := hm.mpr h
    simp only [if_pos hc, boundaryBit, if_pos h]
  · have hc := fun hc => h (hm.mp hc)
    simp only [if_neg hc, boundaryBit, if_neg h]

theorem endpoint_source (margin : Nat) (lo : Bool) (link : Z4Link) (time : Nat) :
    endpointCharge margin lo (!lo) (atTime time link) =
      if time=endpointTime margin lo then boundaryBit margin link else 0 := by
  cases lo <;> simp only [endpointCharge, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, Nat.zero_add, Nat.add_zero, endpointTime]
  · exact cap_indicator margin (margin+3) time link
  · exact cap_indicator margin margin time link

theorem single_cap_cut_decode (margin : Nat) (lo : Bool) (state : EdgeLabelling)
    (hs : (spatialOddFaces margin state).length=1)
    (hc : momentCheck margin lo (!lo) state=true)
    (link : Z4Link) (hd : link.2 ≠ Dir4.x3) (time : Nat) :
    cutCount time link (oddFaces (responseExtent margin) state) =
      ((if endpointTime margin lo ≤ time then boundaryBit margin link else 0) +
        (if singleCapTime margin state ≤ time then boundaryBit margin link else 0)) % 2 := by
  rw [moment_temporal_bit margin lo (!lo) state hc link hd time]
  have he := temporalBit_source_congr
    (fun t => endpointCharge margin lo (!lo) (atTime t link))
    (fun t => faceIncidenceCount (atTime t link) (spatialOddFaces margin state))
    (twoImpulses (endpointTime margin lo) (singleCapTime margin state)
      (boundaryBit margin link) (boundaryBit margin link)) (fun _ => 0)
    (fun t => by
      rw [single_spatial_cap_pin margin lo state hs hc]
      simp only [faceIncidenceCount, Nat.add_zero, endpoint_source, twoImpulses]
      rw [cap_indicator]) time
  exact he.trans (two_impulses_decode _ _ _ _ time)

def between (lower upper time : Nat) : Prop :=
  (lower ≤ time ∧ time < upper) ∨ (upper ≤ time ∧ time < lower)

instance (lower upper time : Nat) : Decidable (between lower upper time) :=
  inferInstanceAs (Decidable ((lower ≤ time ∧ time < upper) ∨ (upper ≤ time ∧ time < lower)))

theorem single_cap_cut_one_iff (margin : Nat) (lo : Bool) (state : EdgeLabelling)
    (hs : (spatialOddFaces margin state).length=1)
    (hc : momentCheck margin lo (!lo) state=true)
    (link : Z4Link) (hd : link.2 ≠ Dir4.x3) (time : Nat) :
    cutCount time link (oddFaces (responseExtent margin) state)=1 ↔
      atTime margin link ∈ edgesOf (sliceFace margin 0) ∧
        between (endpointTime margin lo) (singleCapTime margin state) time := by
  rw [single_cap_cut_decode margin lo state hs hc link hd time]
  by_cases hb : atTime margin link ∈ edgesOf (sliceFace margin 0)
  · have hbv : boundaryBit margin link=1 := if_pos hb
    rw [hbv]
    constructor
    · intro h
      refine ⟨hb,?_⟩
      unfold between
      by_cases hl : endpointTime margin lo ≤ time
      · by_cases hu : singleCapTime margin state ≤ time
        · rw [if_pos hl, if_pos hu] at h
          contradiction
        · exact Or.inl ⟨hl,Nat.lt_of_not_ge hu⟩
      · by_cases hu : singleCapTime margin state ≤ time
        · exact Or.inr ⟨hu,Nat.lt_of_not_ge hl⟩
        · rw [if_neg hl, if_neg hu] at h
          contradiction
    · rintro ⟨_,h⟩
      rcases h with h | h
      · rw [if_pos h.1, if_neg (Nat.not_le_of_lt h.2)]
      · rw [if_neg (Nat.not_le_of_lt h.2), if_pos h.1]
  · have hbv : boundaryBit margin link=0 := if_neg hb
    rw [hbv]
    simp only [ite_self, Nat.zero_add]
    constructor
    · intro h; contradiction
    · intro h; exact False.elim (hb h.1)

theorem single_cap_cut_nonempty_iff (margin : Nat) (lo : Bool) (state : EdgeLabelling)
    (hs : (spatialOddFaces margin state).length=1)
    (hc : momentCheck margin lo (!lo) state=true) (time : Nat) :
    cut time (oddFaces (responseExtent margin) state) ≠ [] ↔
      between (endpointTime margin lo) (singleCapTime margin state) time := by
  constructor
  · intro h
    cases he : cut time (oddFaces (responseExtent margin) state) with
    | nil => exact False.elim (h he)
    | cons link rest =>
      have hm : link ∈ cut time (oddFaces (responseExtent margin) state) := he ▸ List.mem_cons_self
      obtain ⟨face,hf,hlink⟩ := List.mem_map.mp hm
      have hx := of_decide_eq_true (List.mem_filter.mp hf).2
      have ht : atTime time link = link := by
        rw [← hlink]
        have heq := hx.2
        subst time
        rfl
      have hone : cutCount time link (oddFaces (responseExtent margin) state)=1 := by
        rw [cutCount, ht]
        exact occurrenceCount_eq_one_of_mem_nodup _ _ (cut_nodup _ _ (oddFaces_nodup _ _)) hm
      have hd : link.2 ≠ Dir4.x3 := hlink ▸ cutEdge_spatial face
      exact ((single_cap_cut_one_iff margin lo state hs hc link hd time).mp hone).2
  · intro hb
    let link : Z4Link := ((1+margin,1+margin,1+margin,0),.x0)
    have hm : atTime margin link ∈ edgesOf (sliceFace margin 0) := List.mem_cons_self
    have hone := (single_cap_cut_one_iff margin lo state hs hc link
      (by change Dir4.x0 ≠ Dir4.x3; decide) time).mpr ⟨hm,hb⟩
    intro he
    rw [cutCount, he] at hone
    contradiction

end YMGap.Continuum.BF4ExactSlabSingleCapDecoder

#print axioms YMGap.Continuum.BF4ExactSlabSingleCapDecoder.endpointTime
#print axioms YMGap.Continuum.BF4ExactSlabSingleCapDecoder.boundaryBit
#print axioms YMGap.Continuum.BF4ExactSlabSingleCapDecoder.cap_boundary_mem
#print axioms YMGap.Continuum.BF4ExactSlabSingleCapDecoder.cap_indicator
#print axioms YMGap.Continuum.BF4ExactSlabSingleCapDecoder.endpoint_source
#print axioms YMGap.Continuum.BF4ExactSlabSingleCapDecoder.single_cap_cut_decode
#print axioms YMGap.Continuum.BF4ExactSlabSingleCapDecoder.between
#print axioms YMGap.Continuum.BF4ExactSlabSingleCapDecoder.single_cap_cut_one_iff
#print axioms YMGap.Continuum.BF4ExactSlabSingleCapDecoder.single_cap_cut_nonempty_iff
