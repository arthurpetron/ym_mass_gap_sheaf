/-
# A finite injective higher-label code for original zero-spatial short pairs

The code lists the two quotient labels on the original local physical
index list. Original short pairs vanish off that list; accepted moment
parities reconstruct both original labelings. Equal codes therefore mean
equal original pairs, even when their selected supports differ. The code's
sum is exactly the original pairHigher exponent, and each entry has its
explicit cutoff bound. This is a weight-preserving encoding, not a weighted
count of its image or an estimate on the full signed short remainder.
-/

import YMGap.Continuum.BF4ExactSlabShortCoreLocalization
import YMGap.Continuum.BF4ExactSlabZeroSpatialHigherCost

namespace YMGap.Continuum.BF4ExactSlabLocalizedHigherCode

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteParityHigherProduct
open YMGap.Continuum.BF4ExactSlabShortCoreLocalization
open YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow
open YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction
open YMGap.Continuum.BF4ExactSlabZeroSpatialChannels
open YMGap.Continuum.BF4ExactSlabParityHigherPairBound
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

def higherCode (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : List (Nat × Nat) :=
  (shortNearbyIds margin).map (fun id => (pair.1 id/2,pair.2 id/2))

def codeHigher : List (Nat × Nat) → Nat
  | [] => 0
  | entry::rest => entry.1+entry.2+codeHigher rest

theorem higherCode_length (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) :
    (higherCode margin pair).length = (shortNearbyIds margin).length := List.length_map _

theorem higherCode_length_le (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) :
    (higherCode margin pair).length ≤ shortFaceCapacity := by
  rw [higherCode_length]
  exact shortNearbyIds_length_le margin

theorem map_equal_on {A B : Type} (f g : A → B) : ∀ xs : List A,
    xs.map f = xs.map g → ∀ x, x ∈ xs → f x = g x
  | [], _, _, hx => by cases hx
  | head::xs, he, x, hx => by
    have h := List.cons.inj he
    rcases List.mem_cons.mp hx with hx | hx
    · exact hx ▸ h.1
    · exact map_equal_on f g xs h.2 x hx

theorem higherCode_injective {K margin : Nat} {leftIds rightIds : List Nat}
    {left right : EdgeLabelling × EdgeLabelling}
    (hls : leftIds ∈ shortOtherCores 33 margin) (hrs : rightIds ∈ shortOtherCores 33 margin)
    (hlp : left ∈ labels K leftIds) (hrp : right ∈ labels K rightIds)
    (hl0 : spatialOddFaces margin left.1 = []) (hl1 : spatialOddFaces margin left.2 = [])
    (hr0 : spatialOddFaces margin right.1 = []) (hr1 : spatialOddFaces margin right.2 = [])
    (hln : ¬pairTerm margin left.1 left.2 ≈ 0) (hrn : ¬pairTerm margin right.1 right.2 ≈ 0)
    (he : higherCode margin left = higherCode margin right) : left = right := by
  have hlc := nonzero_pair_checks margin left.1 left.2 hl0 hln
  have hrc := nonzero_pair_checks margin right.1 right.2 hr0 hrn
  have hq (id : Nat) (hi : id ∈ shortNearbyIds margin) :
      (left.1 id/2,left.2 id/2) = (right.1 id/2,right.2 id/2) := map_equal_on _ _ _ he id hi
  apply Prod.ext
  · funext id
    by_cases hi : id ∈ shortNearbyIds margin
    · have hphys := nearbyIds_physical hi
      have h := spatial_and_higher_determine_face_label margin true true left.1 right.1 hlc.1 hrc.1
        (hl0.trans hr0.symm) _ (slabPlaquetteAt_mem hphys)
        (by rw [idxOf_slabPlaquetteAt hphys]; exact congrArg Prod.fst (hq id hi))
      rw [idxOf_slabPlaquetteAt hphys] at h
      exact h
    · exact (short_pair_outside hls hlp id hi).1.trans (short_pair_outside hrs hrp id hi).1.symm
  · funext id
    by_cases hi : id ∈ shortNearbyIds margin
    · have hphys := nearbyIds_physical hi
      have h := spatial_and_higher_determine_face_label margin false false left.2 right.2 hlc.2 hrc.2
        (hl1.trans hr1.symm) _ (slabPlaquetteAt_mem hphys)
        (by rw [idxOf_slabPlaquetteAt hphys]; exact congrArg Prod.snd (hq id hi))
      rw [idxOf_slabPlaquetteAt hphys] at h
      exact h
    · exact (short_pair_outside hls hlp id hi).2.trans (short_pair_outside hrs hrp id hi).2.symm

theorem higherCode_bounded {K margin : Nat} {ids : List Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hp : pair ∈ labels K ids) (entry : Nat × Nat) (he : entry ∈ higherCode margin pair) :
    entry.1 ≤ K/2 ∧ entry.2 ≤ K/2 := by
  obtain ⟨id,_,rfl⟩ := List.mem_map.mp he
  have hb := bounded K ids pair hp id
  constructor <;> omega

theorem higherCount_filter (state : Nat → Nat) (keep : Nat → Bool) : ∀ ids : List Nat,
    (∀ id, id ∈ ids → keep id = false → state id = 0) →
      higherCount state ids = higherCount state (ids.filter keep)
  | [], _ => rfl
  | id::ids, h => by
    have ih := higherCount_filter state keep ids (fun j hj hk => h j (List.mem_cons_of_mem id hj) hk)
    cases hk : keep id with
    | true => simpa only [higherCount, List.filter_cons, hk, ↓reduceIte] using congrArg (fun n => state id/2+n) ih
    | false =>
      have hz := h id List.mem_cons_self hk
      simpa only [higherCount, List.filter_cons, hk, Bool.false_eq_true, ↓reduceIte,
        hz, Nat.zero_div, Nat.zero_add] using ih

theorem codeHigher_map (left right : Nat → Nat) : ∀ ids : List Nat,
    codeHigher (ids.map (fun id => (left id/2,right id/2))) = higherCount left ids+higherCount right ids
  | [] => rfl
  | id::ids => by
    have ih := codeHigher_map left right ids
    simp only [List.map_cons, codeHigher, higherCount]
    omega

theorem higherCode_power {K margin : Nat} {ids : List Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hs : ids ∈ shortOtherCores 33 margin) (hp : pair ∈ labels K ids) :
    codeHigher (higherCode margin pair) = pairHigher margin pair := by
  let keep := fun id => decide (SepLatticeZ4Linf.linfDist (sliceFace margin 0)
    (slabPlaquetteAt (responseExtent margin) id) ≤ 33)
  have hout (id : Nat) (hi : id ∈ slabPhysicalFaceEdges (responseExtent margin)) (hk : keep id = false) :
      pair.1 id = 0 ∧ pair.2 id = 0 := by
    apply short_pair_outside hs hp id
    intro hn
    have ht : keep id = true := (List.mem_filter.mp hn).2
    rw [hk] at ht
    cases ht
  have hl := higherCount_filter pair.1 keep (slabPhysicalFaceEdges (responseExtent margin))
    (fun id hi hk => (hout id hi hk).1)
  have hr := higherCount_filter pair.2 keep (slabPhysicalFaceEdges (responseExtent margin))
    (fun id hi hk => (hout id hi hk).2)
  unfold higherCode
  rw [codeHigher_map]
  exact (congrArg (fun n => n+higherCount pair.2 (slabPhysicalFaceEdges (responseExtent margin))) hl).trans
    (congrArg (fun n => higherCount pair.1 (shortNearbyIds margin)+n) hr) |>.symm

end YMGap.Continuum.BF4ExactSlabLocalizedHigherCode

#print axioms YMGap.Continuum.BF4ExactSlabLocalizedHigherCode.higherCode
#print axioms YMGap.Continuum.BF4ExactSlabLocalizedHigherCode.codeHigher
#print axioms YMGap.Continuum.BF4ExactSlabLocalizedHigherCode.higherCode_length
#print axioms YMGap.Continuum.BF4ExactSlabLocalizedHigherCode.higherCode_length_le
#print axioms YMGap.Continuum.BF4ExactSlabLocalizedHigherCode.map_equal_on
#print axioms YMGap.Continuum.BF4ExactSlabLocalizedHigherCode.higherCode_injective
#print axioms YMGap.Continuum.BF4ExactSlabLocalizedHigherCode.higherCode_bounded
#print axioms YMGap.Continuum.BF4ExactSlabLocalizedHigherCode.higherCount_filter
#print axioms YMGap.Continuum.BF4ExactSlabLocalizedHigherCode.codeHigher_map
#print axioms YMGap.Continuum.BF4ExactSlabLocalizedHigherCode.higherCode_power
