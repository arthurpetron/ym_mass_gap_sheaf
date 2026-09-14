/-
# The original leading-power moment has a unique spatial continuation

For fundamental labels confined to the three temporal layers, every
spatial cut bit is the actual lower endpoint charge. The upper endpoint
charge is the same bit. In particular a one-endpoint moment is exactly
zero: the original SU(2) center checker rejects it. This does not evaluate
the mixed moment, the leading coefficient, or the signed remainder.
-/

import YMGap.Continuum.BF4ExactSlabMinimalMomentParity

namespace YMGap.Continuum.BF4ExactSlabMinimalMomentContinuation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4TemporalSpatialIncidence
open YMGap.Continuum.Z4TemporalCutParityMinimum
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4ThreeCutSaturation
open YMGap.Continuum.Z4WindowSpatialParity
open YMGap.Continuum.BF4ExactSlabPositiveFaceCutMinimum
open YMGap.Continuum.BF4ExactSlabMinimalMomentParity
open YMGap.Continuum.BF4ExactSlabMinimalPowerWindow
open YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry

local infix:50 " ≈ " => Q'.eqv

def endpointBit (margin : Nat) (flag : Bool) (link : Z4Link) : Nat :=
  if flag then (if atTime margin link ∈ edgesOf (sliceFace margin 0) then 1 else 0) else 0

theorem endpointBit_le_one (margin : Nat) (flag : Bool) (link : Z4Link) :
    endpointBit margin flag link ≤ 1 := by
  by_cases h : atTime margin link ∈ edgesOf (sliceFace margin 0)
  · cases flag <;> simp [endpointBit,h]
  · cases flag <;> simp [endpointBit,h]

theorem moment_cut_pin (margin : Nat) (lo hi : Bool) (state : EdgeLabelling)
    (hs : ∀ id, id ∈ slabPhysicalFaceEdges (responseExtent margin) → state id ≤ 1)
    (hw : ∀ f, f ∈ positiveFaces (responseExtent margin) state → window margin f = true)
    (hc : momentCheck margin lo hi state = true) (link : Z4Link) (hd : link.2 ≠ .x3) :
    cutCount margin link (positiveFaces (responseExtent margin) state) = endpointBit margin lo link ∧
    cutCount (margin+1) link (positiveFaces (responseExtent margin) state) = endpointBit margin lo link ∧
    cutCount (margin+2) link (positiveFaces (responseExtent margin) state) = endpointBit margin lo link ∧
    endpointBit margin hi link = endpointBit margin lo link := by
  have h0 := moment_geometry_parity margin lo hi state hs hc (atTime (margin+0) link)
  have h1 := moment_geometry_parity margin lo hi state hs hc (atTime (margin+1) link)
  have h2 := moment_geometry_parity margin lo hi state hs hc (atTime (margin+2) link)
  have h3 := moment_geometry_parity margin lo hi state hs hc (atTime (margin+3) link)
  simp only [endpointCharge, retimed_endpoint_mem] at h0 h1 h2 h3
  apply window_parity_unique margin link hd _ (positiveFaces_nodup _ _) hw
    _ _ (endpointBit_le_one margin lo link) (endpointBit_le_one margin hi link)
  · simpa [endpointBit] using h0
  · simpa using h1
  · simpa using h2
  · simpa [endpointBit, Nat.add_comm] using h3

theorem accepted_flags_equal (margin : Nat) (lo hi : Bool) (state : EdgeLabelling)
    (hs : ∀ id, id ∈ slabPhysicalFaceEdges (responseExtent margin) → state id ≤ 1)
    (hw : ∀ f, f ∈ positiveFaces (responseExtent margin) state → window margin f = true)
    (hc : momentCheck margin lo hi state = true) : lo = hi := by
  let link : Z4Link := ((1+margin,1+margin,1+margin,0),.x0)
  have he := (moment_cut_pin margin lo hi state hs hw hc link
    (by change Dir4.x0 ≠ Dir4.x3; decide)).2.2.2
  have hm : atTime margin link ∈ edgesOf (sliceFace margin 0) := by
    simp [atTime,link,sliceFace,edgesOf,dirsOf]
  unfold endpointBit at he
  rw [if_pos hm] at he
  cases lo <;> cases hi <;> simp_all

theorem one_endpoint_check_false (margin : Nat) (lo hi : Bool) (state : EdgeLabelling)
    (hne : lo ≠ hi)
    (hs : ∀ id, id ∈ slabPhysicalFaceEdges (responseExtent margin) → state id ≤ 1)
    (hw : ∀ f, f ∈ positiveFaces (responseExtent margin) state → window margin f = true) :
    momentCheck margin lo hi state = false := by
  cases hc : momentCheck margin lo hi state with
  | false => rfl
  | true => exact False.elim (hne (accepted_flags_equal margin lo hi state hs hw hc))

theorem one_endpoint_zero (margin : Nat) (lo hi : Bool) (state : EdgeLabelling)
    (hne : lo ≠ hi)
    (hs : ∀ id, id ∈ slabPhysicalFaceEdges (responseExtent margin) → state id ≤ 1)
    (hw : ∀ f, f ∈ positiveFaces (responseExtent margin) state → window margin f = true) :
    moment margin lo hi state ≈ 0 :=
  moment_rejected margin lo hi state (one_endpoint_check_false margin lo hi state hne hs hw)

theorem accepted_partition_empty (margin : Nat) (state : EdgeLabelling)
    (hs : ∀ id, id ∈ slabPhysicalFaceEdges (responseExtent margin) → state id ≤ 1)
    (hw : ∀ f, f ∈ positiveFaces (responseExtent margin) state → window margin f = true)
    (hc : momentCheck margin false false state = true) :
    positiveFaces (responseExtent margin) state = [] := by
  have hnone (f : Z4Plaq) (hf : f ∈ positiveFaces (responseExtent margin) state) : False := by
    have hd : (cutEdge f).2 ≠ Dir4.x3 := by
      rcases f with ⟨v,p⟩
      cases p <;> simp [cutEdge,dirsOf]
    have hh := moment_cut_pin margin false false state hs hw hc (cutEdge f) hd
    simp only [endpointBit, Bool.false_eq_true, ↓reduceIte] at hh
    have ht := hw f hf
    have hx : crosses f.1.2.2.2 f = true := decide_eq_true ⟨window_temporal ht,rfl⟩
    have hm : cutEdge f ∈ cut f.1.2.2.2 (positiveFaces (responseExtent margin) state) :=
      List.mem_map.mpr ⟨f,List.mem_filter.mpr ⟨hf,hx⟩,rfl⟩
    have hone : cutCount f.1.2.2.2 (cutEdge f) (positiveFaces (responseExtent margin) state) = 1 := by
      have he : atTime f.1.2.2.2 (cutEdge f) = cutEdge f := rfl
      rw [cutCount,he]
      exact occurrenceCount_eq_one_of_mem_nodup _ _
        (cut_nodup _ _ (positiveFaces_nodup _ _)) hm
    rcases window_times ht with h | h | h
    · rw [h,hh.1] at hone
      cases hone
    · rw [h,hh.2.1] at hone
      cases hone
    · rw [h,hh.2.2.1] at hone
      cases hone
  cases he : positiveFaces (responseExtent margin) state with
  | nil => rfl
  | cons f fs =>
    apply False.elim
    apply hnone f
    rw [he]
    exact List.mem_cons_self

/-- The SAME signed four-moment term at original leading power has no mean product. -/
theorem retained_minimal_pairTerm {K margin time : Nat} {selected : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : selected ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ (((labels K selected).filter (pairKeep margin time)).filter (pairLeafKeep margin)))
    (he : pairPower margin pair = 36) :
    pairTerm margin pair.1 pair.2 ≈
      moment margin true true pair.1 * moment margin false false pair.2 := by
  have hb := (retained_minimal_power_fundamental hs hp he).2
  have hw := (retained_minimal_window hs hp he).1
  have hz := one_endpoint_zero margin true false pair.1 (by decide)
    (fun id hi => (hb id hi).1) hw
  have hprod : moment margin true false pair.1 * moment margin false true pair.2 ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hz) (Q'.zero_mul_eqv _)
  have hn : -(moment margin true false pair.1 * moment margin false true pair.2) ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hprod) (by decide)
  exact Q'.eqv_trans _ _ _ (pairTerm_pin margin pair.1 pair.2)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) hn)
      (Q'.eqv_of_eq (Q'.add_zero' _)))

/-- A leading original pair with any occupied partition-replica face contributes zero. -/
theorem retained_nonempty_partition_zero {K margin time : Nat} {selected : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : selected ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ (((labels K selected).filter (pairKeep margin time)).filter (pairLeafKeep margin)))
    (he : pairPower margin pair = 36)
    (hn : positiveFaces (responseExtent margin) pair.2 ≠ []) : pairTerm margin pair.1 pair.2 ≈ 0 := by
  have hb := (retained_minimal_power_fundamental hs hp he).2
  have hw := (retained_minimal_window hs hp he).2
  have hz : moment margin false false pair.2 ≈ 0 := by
    cases hc : momentCheck margin false false pair.2 with
    | false => exact moment_rejected margin false false pair.2 hc
    | true => exact False.elim (hn (accepted_partition_empty margin pair.2
        (fun id hi => (hb id hi).2) hw hc))
  exact Q'.eqv_trans _ _ _ (retained_minimal_pairTerm hs hp he)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (Q'.mul_zero_eqv _))

end YMGap.Continuum.BF4ExactSlabMinimalMomentContinuation

#print axioms YMGap.Continuum.BF4ExactSlabMinimalMomentContinuation.endpointBit_le_one
#print axioms YMGap.Continuum.BF4ExactSlabMinimalMomentContinuation.moment_cut_pin
#print axioms YMGap.Continuum.BF4ExactSlabMinimalMomentContinuation.accepted_flags_equal
#print axioms YMGap.Continuum.BF4ExactSlabMinimalMomentContinuation.one_endpoint_check_false
#print axioms YMGap.Continuum.BF4ExactSlabMinimalMomentContinuation.one_endpoint_zero
#print axioms YMGap.Continuum.BF4ExactSlabMinimalMomentContinuation.accepted_partition_empty
#print axioms YMGap.Continuum.BF4ExactSlabMinimalMomentContinuation.retained_minimal_pairTerm
#print axioms YMGap.Continuum.BF4ExactSlabMinimalMomentContinuation.retained_nonempty_partition_zero
