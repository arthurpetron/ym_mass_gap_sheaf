/-
# Four original spatial occurrences have a bounded two-anchor code

The original projected cycle forces one of three pairings. A replica split,
two literal local faces and two local times recover both ordered spatial
lists. The computed target has at most 5*3*shortFaceCapacity^2*67^2 entries.
It is not evaluated or substituted for the original configuration list.
Higher labels are separate data, needed to recover the complete pair.
-/

import YMGap.Continuum.BF4ExactSlabProjectedSpatialCycle
import YMGap.Continuum.Z4FourProjectedFaceCode
import YMGap.Continuum.BF4ExactSlabTwoCapLocalCode

namespace YMGap.Continuum.BF4ExactSlabFourCapLocalCode

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.Z4SpatialPlaquetteProjection
open YMGap.Continuum.Z4FourFaceClosedPairing
open YMGap.Continuum.Z4FourProjectedFaceCode
open YMGap.Continuum.BF4ExactSlabProjectedSpatialCycle
open YMGap.Continuum.BF4ExactSlabTwoCapSpatialCode
open YMGap.Continuum.BF4ExactSlabTwoCapLocalCode (localFaces spatialList_local localFace_time cartesian_length)
open YMGap.Continuum.BF4ExactSlabSingleSpatialCap (capFace)
open YMGap.Continuum.BF4ExactSlabPairChannelParity
open YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction
open YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow
open YMGap.Continuum.BF4ExactSlabShortCoreLocalization
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.PairedPositiveFaceLabellings

local infix:50 " ≈ " => Q'.eqv
local instance : DecidableEq Z4Plaq := inferInstanceAs (DecidableEq (Z4Vertex × Z4Plane))

def cap (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) (index : Nat) : Z4Plaq :=
  ((spatialList margin pair).drop index).headD (capFace margin 0)

theorem spatialList_four (margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (hs : pairSpatial margin pair=4) :
    spatialList margin pair=[cap margin pair 0,cap margin pair 1,cap margin pair 2,cap margin pair 3] := by
  have hl : (spatialList margin pair).length=4 := by rw [spatialList,List.length_append]; exact hs
  cases he : spatialList margin pair with
  | nil => simp only [he,List.length_nil] at hl; omega
  | cons a rest =>
    cases rest with
    | nil => simp only [he,List.length_cons,List.length_nil] at hl; omega
    | cons b rest =>
      cases rest with
      | nil => simp only [he,List.length_cons,List.length_nil] at hl; omega
      | cons c rest =>
        cases rest with
        | nil => simp only [he,List.length_cons,List.length_nil] at hl; omega
        | cons d rest =>
          have ht : rest=[] := List.length_eq_zero_iff.mp (by
            simp only [he,List.length_cons] at hl; omega)
          subst rest
          simp only [cap,he,List.drop_zero,List.drop_succ_cons,List.headD_cons]

theorem original_four_cap_pairing (margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0) (hs : pairSpatial margin pair=4) :
    (faceAt 0 (cap margin pair 0)=faceAt 0 (cap margin pair 1) ∧
      faceAt 0 (cap margin pair 2)=faceAt 0 (cap margin pair 3)) ∨
    (faceAt 0 (cap margin pair 0)=faceAt 0 (cap margin pair 2) ∧
      faceAt 0 (cap margin pair 1)=faceAt 0 (cap margin pair 3)) ∨
    (faceAt 0 (cap margin pair 0)=faceAt 0 (cap margin pair 3) ∧
      faceAt 0 (cap margin pair 1)=faceAt 0 (cap margin pair 2)) := by
  apply closed_four_pairing
  intro link
  have h := original_projectedFaces_closed margin pair hne link
  simpa only [projectedFaces,spatialList_four margin pair hs,List.map_cons,List.map_nil] using h

def code (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Nat × Code :=
  (layout margin pair,encode (margin-33) (cap margin pair 0) (cap margin pair 1)
    (cap margin pair 2) (cap margin pair 3))

def codes (margin : Nat) : List (Nat × Code) :=
  cartesian (List.range 5) (cartesian (List.range 3) (cartesian (localFaces margin)
    (cartesian (localFaces margin) (cartesian (List.range 67) (List.range 67)))))

def spatialCapacity : Nat := 5*3*shortFaceCapacity^2*67^2

theorem codes_length_le (margin : Nat) : (codes margin).length ≤ spatialCapacity := by
  simp only [codes,cartesian_length,List.length_range,localFaces,List.length_map]
  have h := shortNearbyIds_length_le margin
  have h' := Nat.mul_le_mul h (Nat.mul_le_mul_right (67*67) h)
  have h'' := Nat.mul_le_mul_left 5 (Nat.mul_le_mul_left 3 h')
  simpa only [spatialCapacity,Nat.pow_succ,Nat.pow_zero,Nat.mul_one,Nat.mul_assoc] using h''

theorem caps_local {K margin : Nat} {ids : List Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hs : ids ∈ shortOtherCores 33 margin) (hp : pair ∈ labels K ids)
    (hsp : pairSpatial margin pair=4) (index : Nat) (hi : index < 4) :
    cap margin pair index ∈ localFaces margin := by
  have hl := spatialList_four margin pair hsp
  apply spatialList_local hs hp
  rw [hl]
  have hindex : index=0 ∨ index=1 ∨ index=2 ∨ index=3 := by omega
  rcases hindex with rfl | rfl | rfl | rfl <;> simp only [List.mem_cons,List.not_mem_nil,or_false,true_or,or_true]

theorem code_mem {K margin : Nat} {ids : List Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hs : ids ∈ shortOtherCores 33 margin) (hp : pair ∈ labels K ids)
    (hsp : pairSpatial margin pair=4) : code margin pair ∈ codes margin := by
  have h0 := caps_local hs hp hsp 0 (by decide)
  have h1 := caps_local hs hp hsp 1 (by decide)
  have h2 := caps_local hs hp hsp 2 (by decide)
  have h3 := caps_local hs hp hsp 3 (by decide)
  have ht1 := (localFace_time margin _ h1).2
  have ht2 := (localFace_time margin _ h2).2
  have ht3 := (localFace_time margin _ h3).2
  have hl : layout margin pair < 5 := by unfold pairSpatial at hsp; unfold layout; omega
  unfold code codes
  apply (mem_cartesian_iff _ _ _).mpr
  refine ⟨List.mem_range.mpr hl,?_⟩
  unfold encode
  split <;> (try split)
  all_goals simp only [mem_cartesian_iff,List.mem_range]
  · exact ⟨by decide,h0,h2,ht1,ht3⟩
  · exact ⟨by decide,h0,h1,ht2,ht3⟩
  · exact ⟨by decide,h0,h1,ht3,ht2⟩

theorem decode_code {K margin : Nat} {ids : List Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hs : ids ∈ shortOtherCores 33 margin) (hp : pair ∈ labels K ids)
    (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0) (hsp : pairSpatial margin pair=4) :
    decode (margin-33) (code margin pair).2=spatialList margin pair := by
  exact (decode_encode (margin-33) _ _ _ _ (original_four_cap_pairing margin pair hne hsp)
    (localFace_time margin _ (caps_local hs hp hsp 1 (by decide))).1
    (localFace_time margin _ (caps_local hs hp hsp 2 (by decide))).1
    (localFace_time margin _ (caps_local hs hp hsp 3 (by decide))).1).trans
      (spatialList_four margin pair hsp).symm

theorem code_recover_spatial {K margin : Nat} {leftIds rightIds : List Nat}
    {left right : EdgeLabelling × EdgeLabelling}
    (hls : leftIds ∈ shortOtherCores 33 margin) (hrs : rightIds ∈ shortOtherCores 33 margin)
    (hlp : left ∈ labels K leftIds) (hrp : right ∈ labels K rightIds)
    (hln : ¬pairTerm margin left.1 left.2 ≈ 0) (hrn : ¬pairTerm margin right.1 right.2 ≈ 0)
    (hl : pairSpatial margin left=4) (hr : pairSpatial margin right=4)
    (he : code margin left=code margin right) :
    spatialOddFaces margin left.1=spatialOddFaces margin right.1 ∧
      spatialOddFaces margin left.2=spatialOddFaces margin right.2 := by
  have hc := congrArg (fun x : Nat × Code => decode (margin-33) x.2) he
  dsimp only at hc
  rw [decode_code hls hlp hln hl,decode_code hrs hrp hrn hr] at hc
  exact append_split_injective _ _ _ _ (congrArg Prod.fst he) hc

end YMGap.Continuum.BF4ExactSlabFourCapLocalCode

#print axioms YMGap.Continuum.BF4ExactSlabFourCapLocalCode.cap
#print axioms YMGap.Continuum.BF4ExactSlabFourCapLocalCode.spatialList_four
#print axioms YMGap.Continuum.BF4ExactSlabFourCapLocalCode.original_four_cap_pairing
#print axioms YMGap.Continuum.BF4ExactSlabFourCapLocalCode.code
#print axioms YMGap.Continuum.BF4ExactSlabFourCapLocalCode.codes
#print axioms YMGap.Continuum.BF4ExactSlabFourCapLocalCode.spatialCapacity
#print axioms YMGap.Continuum.BF4ExactSlabFourCapLocalCode.codes_length_le
#print axioms YMGap.Continuum.BF4ExactSlabFourCapLocalCode.caps_local
#print axioms YMGap.Continuum.BF4ExactSlabFourCapLocalCode.code_mem
#print axioms YMGap.Continuum.BF4ExactSlabFourCapLocalCode.decode_code
#print axioms YMGap.Continuum.BF4ExactSlabFourCapLocalCode.code_recover_spatial
