/-
# A bounded spatial code for every original two-cap short pair

The code keeps the replica split, the first literal cap, and the second
cap's time relative to the fixed local window. Parallel projection recovers
the second cap. The explicit target list has at most 3*67*shortFaceCapacity
entries, uniformly in cutoff and margin; it is not evaluated. This codes
spatial parity data only. Higher-label data are still needed for a pair.
-/

import YMGap.Continuum.BF4ExactSlabTwoCapSpatialCode
import YMGap.Continuum.BF4ExactSlabShortCoreLocalization
import YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
import YMGap.Continuum.FiniteWeightedCartesianInjection

namespace YMGap.Continuum.BF4ExactSlabTwoCapLocalCode

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.Z4LinfFiniteRegion
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4SpatialPlaquetteProjection
open YMGap.Continuum.BF4ExactSlabTwoCapSpatialCode
open YMGap.Continuum.BF4ExactSlabShortCoreLocalization
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow
open YMGap.Continuum.BF4ExactSlabOddFaceIncidence
open YMGap.Continuum.BF4ExactSlabPairChannelParity
open YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

def localFaces (margin : Nat) : List Z4Plaq :=
  (shortNearbyIds margin).map (slabPlaquetteAt (responseExtent margin))

theorem local_odd_face (margin : Nat) (state : EdgeLabelling)
    (hout : ∀ id, id ∉ shortNearbyIds margin → state id=0)
    (face : Z4Plaq) (hf : face ∈ oddFaces (responseExtent margin) state) : face ∈ localFaces margin := by
  have hphys := oddFaces_physical hf
  rw [← slabFaceIds_map] at hphys
  obtain ⟨id,hi,rfl⟩ := List.mem_map.mp hphys
  have hb := of_decide_eq_true (List.mem_filter.mp hf).2
  rw [idxOf_slabPlaquetteAt hi] at hb
  have hn : id ∈ shortNearbyIds margin := by
    by_cases hn : id ∈ shortNearbyIds margin
    · exact hn
    · rw [hout id hn] at hb
      contradiction
  exact List.mem_map.mpr ⟨id,hn,rfl⟩

theorem spatialList_local {K margin : Nat} {ids : List Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hs : ids ∈ shortOtherCores 33 margin) (hp : pair ∈ labels K ids)
    (face : Z4Plaq) (hf : face ∈ spatialList margin pair) : face ∈ localFaces margin := by
  rcases List.mem_append.mp hf with hf | hf
  · exact local_odd_face margin pair.1 (fun id hi => (short_pair_outside hs hp id hi).1)
      face (List.mem_filter.mp hf).1
  · exact local_odd_face margin pair.2 (fun id hi => (short_pair_outside hs hp id hi).2)
      face (List.mem_filter.mp hf).1

theorem localFace_time (margin : Nat) (face : Z4Plaq) (hf : face ∈ localFaces margin) :
    margin-33 ≤ face.1.2.2.2 ∧ face.1.2.2.2-(margin-33) < 67 := by
  obtain ⟨id,hi,rfl⟩ := List.mem_map.mp hf
  have hd := of_decide_eq_true (List.mem_filter.mp hi).2
  have ht := Nat.le_trans (le_linfDist_comp (sliceFace margin 0)
    (slabPlaquetteAt (responseExtent margin) id) .x3) hd
  exact coordinate_window _ _ 33 ht

def capCode (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Nat × Z4Plaq × Nat :=
  (layout margin pair,firstCap margin pair,(secondCap margin pair).1.2.2.2-(margin-33))

def capCodes (margin : Nat) : List (Nat × Z4Plaq × Nat) :=
  cartesian (List.range 3) (cartesian (localFaces margin) (List.range 67))

def spatialCapacity : Nat := 3*shortFaceCapacity*67

theorem cartesian_length {A B : Type} : ∀ (xs : List A) (ys : List B),
    (cartesian xs ys).length=xs.length*ys.length
  | [], _ => by simp only [cartesian,List.flatMap_nil,List.length_nil,Nat.zero_mul]
  | x::xs, ys => by
    simp only [cartesian,List.flatMap_cons,List.length_append,List.length_map,
      List.length_cons,Nat.add_mul,Nat.one_mul]
    rw [show (xs.flatMap (fun a => ys.map (fun b => (a,b)))).length=xs.length*ys.length from cartesian_length xs ys]
    exact Nat.add_comm _ _

theorem capCodes_length_le (margin : Nat) : (capCodes margin).length ≤ spatialCapacity := by
  rw [capCodes,cartesian_length,List.length_range,cartesian_length,List.length_range,
    localFaces,List.length_map]
  have h := Nat.mul_le_mul_left 3 (Nat.mul_le_mul_right 67 (shortNearbyIds_length_le margin))
  simpa only [Nat.mul_assoc,spatialCapacity] using h

theorem capCode_mem {K margin : Nat} {ids : List Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hs : ids ∈ shortOtherCores 33 margin) (hp : pair ∈ labels K ids)
    (hsp : pairSpatial margin pair=2) : capCode margin pair ∈ capCodes margin := by
  have hl := spatialList_two margin pair hsp
  have hf := spatialList_local hs hp (firstCap margin pair) (hl ▸ List.mem_cons_self)
  have ht := localFace_time margin (secondCap margin pair)
    (spatialList_local hs hp _ (hl ▸ List.mem_cons_of_mem _ List.mem_cons_self))
  apply (mem_cartesian_iff _ _ _).mpr
  constructor
  · apply List.mem_range.mpr
    unfold pairSpatial at hsp
    change (spatialOddFaces margin pair.1).length < 3
    omega
  · exact (mem_cartesian_iff _ _ _).mpr ⟨hf,List.mem_range.mpr ht.2⟩

theorem capCode_recover_spatial {K margin : Nat} {leftIds rightIds : List Nat}
    {left right : EdgeLabelling × EdgeLabelling}
    (hls : leftIds ∈ shortOtherCores 33 margin) (hrs : rightIds ∈ shortOtherCores 33 margin)
    (hlp : left ∈ labels K leftIds) (hrp : right ∈ labels K rightIds)
    (hln : ¬pairTerm margin left.1 left.2 ≈ 0) (hrn : ¬pairTerm margin right.1 right.2 ≈ 0)
    (hl : pairSpatial margin left=2) (hr : pairSpatial margin right=2)
    (he : capCode margin left=capCode margin right) :
    spatialOddFaces margin left.1=spatialOddFaces margin right.1 ∧
      spatialOddFaces margin left.2=spatialOddFaces margin right.2 := by
  have hf : firstCap margin left=firstCap margin right := congrArg (fun x => x.2.1) he
  have ho : (secondCap margin left).1.2.2.2-(margin-33)=
      (secondCap margin right).1.2.2.2-(margin-33) := congrArg (fun x => x.2.2) he
  have hlt := (localFace_time margin _ (spatialList_local hls hlp _
    (spatialList_two margin left hl ▸ List.mem_cons_of_mem _ List.mem_cons_self))).1
  have hrt := (localFace_time margin _ (spatialList_local hrs hrp _
    (spatialList_two margin right hr ▸ List.mem_cons_of_mem _ List.mem_cons_self))).1
  have ht : (secondCap margin left).1.2.2.2=(secondCap margin right).1.2.2.2 := by omega
  have hp := (two_caps_projection margin left hln hl).symm.trans
    ((congrArg (faceAt 0) hf).trans (two_caps_projection margin right hrn hr))
  exact two_caps_recover_spatial hl hr hf (projection_and_time_injective _ _ hp ht)
    (congrArg Prod.fst he)

end YMGap.Continuum.BF4ExactSlabTwoCapLocalCode

#print axioms YMGap.Continuum.BF4ExactSlabTwoCapLocalCode.localFaces
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapLocalCode.local_odd_face
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapLocalCode.spatialList_local
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapLocalCode.localFace_time
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapLocalCode.capCode
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapLocalCode.capCodes
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapLocalCode.spatialCapacity
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapLocalCode.cartesian_length
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapLocalCode.capCodes_length_le
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapLocalCode.capCode_mem
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapLocalCode.capCode_recover_spatial
