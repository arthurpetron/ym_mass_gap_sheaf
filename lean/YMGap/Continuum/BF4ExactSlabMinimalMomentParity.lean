/-
# Original fundamental moment checks give geometric spatial parity

This pins the existing all-link insertion checker to positive-face
incidence when every original physical label is at most one. The pin
also holds outside the physical link list, where every term is zero.
Retiming preserves the actual endpoint plaquette boundaries.
-/

import YMGap.Continuum.BF4ExactSlabMinimalPowerWindow
import YMGap.Continuum.Z4WindowSpatialParity

namespace YMGap.Continuum.BF4ExactSlabMinimalMomentParity

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4TemporalSpatialIncidence
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.BF4ExactSlabCenterCharge
open YMGap.Continuum.BF4ExactSlabOddFaceIncidence
open YMGap.Continuum.BF4ExactSlabPositiveFaceCutMinimum
open YMGap.Continuum.BF4ExactSlabMinimalPowerWindow
open YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabConnectedTemporalCrossing

def endpointCharge (margin : Nat) (lo hi : Bool) (link : Z4Link) : Nat :=
  (if lo then (if link ∈ edgesOf (sliceFace margin 0) then 1 else 0) else 0) +
    (if hi then (if link ∈ edgesOf (sliceFace margin 3) then 1 else 0) else 0)

theorem moment_geometry_parity (margin : Nat) (lo hi : Bool) (state : EdgeLabelling)
    (hs : ∀ id, id ∈ slabPhysicalFaceEdges (responseExtent margin) → state id ≤ 1)
    (hc : momentCheck margin lo hi state = true) (link : Z4Link) :
    (endpointCharge margin lo hi link +
      faceIncidenceCount link (positiveFaces (responseExtent margin) state)) % 2 = 0 := by
  by_cases hl : link ∈ boundaryCompleteSlabLinks (responseExtent margin)
  · have hh := List.all_eq_true.mp hc ((boundaryCompleteSlabLinks (responseExtent margin)).idxOf link)
      (List.mem_range.mpr (List.idxOf_lt_length_of_mem hl))
    have hp := of_decide_eq_true hh
    change (charges margin lo hi _ + totalCharge (responseExtent margin) _ state) % 2 = 0 at hp
    have hcharges : charges margin lo hi ((boundaryCompleteSlabLinks (responseExtent margin)).idxOf link) =
        endpointCharge margin lo hi link := by
      unfold charges endpointCharge
      rw [faceDegree_pin _ _ _ hl (slice_physical margin ⟨0,by decide⟩),
        faceDegree_pin _ _ _ hl (slice_physical margin ⟨3,by decide⟩)]
    rw [hcharges] at hp
    rw [Nat.add_mod, totalCharge_parity (responseExtent margin) state link hl,
      ← positive_eq_odd _ _ hs] at hp
    rw [Nat.add_mod]
    exact hp
  · have h0 : link ∉ edgesOf (sliceFace margin 0) := fun h => hl
      ((mem_boundaryCompleteSlabLinks_iff _ _).mpr ⟨_,slice_physical margin ⟨0,by decide⟩,h⟩)
    have h3 : link ∉ edgesOf (sliceFace margin 3) := fun h => hl
      ((mem_boundaryCompleteSlabLinks_iff _ _).mpr ⟨_,slice_physical margin ⟨3,by decide⟩,h⟩)
    rw [incidence_outside (responseExtent margin) link hl _ (fun _ hf => positiveFaces_physical hf)]
    cases lo <;> cases hi <;> simp [endpointCharge, h0, h3]

theorem atTime_twice (s t : Nat) (link : Z4Link) : atTime s (atTime t link) = atTime s link := rfl

theorem retime_slice_edges (margin source target : Nat) :
    (edgesOf (sliceFace margin source)).map (atTime (margin+target)) = edgesOf (sliceFace margin target) := rfl

theorem retimed_endpoint_mem (margin offset target : Nat) (link : Z4Link) :
    atTime (margin+offset) link ∈ edgesOf (sliceFace margin target) ↔
      offset = target ∧ atTime margin link ∈ edgesOf (sliceFace margin 0) := by
  constructor
  · intro h
    have ht := endpoint_link_time margin target (atTime (margin+offset) link) h
    have he : offset = target := by change margin+offset = margin+target at ht; omega
    have hm := List.mem_map.mpr ⟨atTime (margin+offset) link,h,atTime_twice margin (margin+offset) link⟩
    have hr := retime_slice_edges margin target 0
    rw [Nat.add_zero] at hr
    exact ⟨he,hr ▸ hm⟩
  · rintro ⟨he,h⟩
    subst offset
    rw [← retime_slice_edges margin 0 target]
    exact List.mem_map.mpr ⟨atTime margin link,h,atTime_twice (margin+target) margin link⟩

end YMGap.Continuum.BF4ExactSlabMinimalMomentParity

#print axioms YMGap.Continuum.BF4ExactSlabMinimalMomentParity.moment_geometry_parity
#print axioms YMGap.Continuum.BF4ExactSlabMinimalMomentParity.atTime_twice
#print axioms YMGap.Continuum.BF4ExactSlabMinimalMomentParity.retime_slice_edges
#print axioms YMGap.Continuum.BF4ExactSlabMinimalMomentParity.retimed_endpoint_mem
