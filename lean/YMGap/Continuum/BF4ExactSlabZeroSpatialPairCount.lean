/-
# Mass-stratified counting of the ORIGINAL zero-spatial short pairs

The source is the actual short-other-core list and its original cut/leaf
filtered representation lists, with zero-spatial and nonzero-moment tests.
No pair is deduplicated or replaced. Its duplicate-free property follows
from original selected-support uniqueness. Local higher-label profiles
inject into words of length H over at most 2*shortFaceCapacity symbols.
Thus the H-stratum has at most (2*shortFaceCapacity)^H original pairs,
with no cutoff or volume factor. H>=1 is derived, not assumed, off the tube.
-/

import YMGap.Continuum.BF4ExactSlabLocalizedHigherCode
import YMGap.Continuum.FiniteOccupationUnitCode

namespace YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.PairedPositiveFaceLabellingUniqueness
open YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow
open YMGap.Continuum.BF4ExactSlabShortCoreLocalization
open YMGap.Continuum.BF4ExactSlabLocalizedHigherCode
open YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount
open YMGap.Continuum.BF4ExactSlabLeadingCountUniqueness
open YMGap.Continuum.BF4ExactSlabShiftedProbeCoveredExpansion (selected_nodup)
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter
open YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction
open YMGap.Continuum.BF4ExactSlabZeroSpatialHigherCost
open YMGap.Continuum.BF4ExactSlabParityHigherPairBound
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.FiniteOccupationUnitCode

local infix:50 " ≈ " => Q'.eqv

def flatten : List (Nat × Nat) → List Nat
  | [] => []
  | entry::rest => entry.1::entry.2::flatten rest

theorem flatten_injective : ∀ left right : List (Nat × Nat), flatten left = flatten right → left = right
  | [], [], _ => rfl
  | [], _::_, he => by cases he
  | _::_, [], he => by cases he
  | (a,b)::left, (c,d)::right, he => by
    have h0 := List.cons.inj he
    have h1 := List.cons.inj h0.2
    dsimp only at h0 h1
    rw [h0.1, h1.1, flatten_injective left right h1.2]

theorem flatten_length : ∀ code : List (Nat × Nat), (flatten code).length = 2*code.length
  | [] => rfl
  | _::rest => by
    have ih := flatten_length rest
    simp only [flatten, List.length_cons]
    omega

theorem flatten_mass : ∀ code : List (Nat × Nat), mass (flatten code) = codeHigher code
  | [] => rfl
  | _::rest => by
    have ih := flatten_mass rest
    simp only [flatten, mass, codeHigher]
    omega

def profile (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : List Nat := flatten (higherCode margin pair)

theorem profile_length (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) :
    (profile margin pair).length = 2*(shortNearbyIds margin).length := by
  rw [profile, flatten_length, higherCode_length]

theorem profile_mass {K margin : Nat} {ids : List Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hs : ids ∈ shortOtherCores 33 margin) (hp : pair ∈ labels K ids) :
    mass (profile margin pair) = pairHigher margin pair :=
  (flatten_mass _).trans (higherCode_power hs hp)

def zeroSpatialKeep (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Bool :=
  decide (spatialOddFaces margin pair.1 = [] ∧ spatialOddFaces margin pair.2 = [] ∧
    ¬pairTerm margin pair.1 pair.2 ≈ 0)

def shortPairs (K margin time : Nat) : List (EdgeLabelling × EdgeLabelling) :=
  (shortOtherCores 33 margin).flatMap (fun ids =>
    (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)))

def zeroSpatialPairs (K margin time : Nat) : List (EdgeLabelling × EdgeLabelling) :=
  (shortPairs K margin time).filter (zeroSpatialKeep margin)

theorem zeroSpatialPairs_mem {K margin time : Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hp : pair ∈ zeroSpatialPairs K margin time) :
    (spatialOddFaces margin pair.1 = [] ∧ spatialOddFaces margin pair.2 = [] ∧
      ¬pairTerm margin pair.1 pair.2 ≈ 0) ∧
    ∃ ids, ids ∈ shortOtherCores 33 margin ∧ pair ∈ labels K ids := by
  have hk := of_decide_eq_true (List.mem_filter.mp hp).2
  obtain ⟨ids,hs,hm⟩ := List.mem_flatMap.mp (List.mem_filter.mp hp).1
  exact ⟨hk,ids,hs,(List.mem_filter.mp (List.mem_filter.mp hm).1).1⟩

theorem shortPairs_nodup (K margin time : Nat) : (shortPairs K margin time).Nodup := by
  have hn : (shortOtherCores 33 margin).Nodup :=
    (((connecting_nodup _ _ _ _ (CayleyParentInj.range_nodup _)).filter _).filter _).filter _
  apply flatMap_nodup _ _ hn
  · intro ids hs
    exact ((labels_nodup K ids (selected_nodup (CayleyParentInj.range_nodup _)
      (connecting_selected (shortOtherCores_connecting hs)))).filter _).filter _
  · intro left hl right hr hne pair hp hq
    exact hne (selected_support_eq (CayleyParentInj.range_nodup _)
      (connecting_selected (shortOtherCores_connecting hl)) (connecting_selected (shortOtherCores_connecting hr))
      (List.mem_filter.mp (List.mem_filter.mp hp).1).1 (List.mem_filter.mp (List.mem_filter.mp hq).1).1)

theorem zeroSpatialPairs_nodup (K margin time : Nat) : (zeroSpatialPairs K margin time).Nodup :=
  (shortPairs_nodup K margin time).filter _

theorem profile_injective_on {K margin time : Nat} {left right : EdgeLabelling × EdgeLabelling}
    (hl : left ∈ zeroSpatialPairs K margin time) (hr : right ∈ zeroSpatialPairs K margin time)
    (he : profile margin left = profile margin right) : left = right := by
  obtain ⟨hlc,leftIds,hls,hlp⟩ := zeroSpatialPairs_mem hl
  obtain ⟨hrc,rightIds,hrs,hrp⟩ := zeroSpatialPairs_mem hr
  exact higherCode_injective hls hrs hlp hrp hlc.1 hlc.2.1 hrc.1 hrc.2.1 hlc.2.2 hrc.2.2
    (flatten_injective _ _ he)

def replicaCapacity : Nat := 2*shortFaceCapacity

theorem zeroSpatialPairs_higher_positive {K margin time : Nat} (hK : 1 ≤ K)
    {pair : EdgeLabelling × EdgeLabelling} (hp : pair ∈ zeroSpatialPairs K margin time) :
    1 ≤ pairHigher margin pair := by
  obtain ⟨hc,ids,hs,hm⟩ := zeroSpatialPairs_mem hp
  exact nonTube_nonzero_higher hK (connecting_selected (shortOtherCores_connecting hs)) hm
    (shortOtherCores_window hs).2.2 hc.1 hc.2.1 hc.2.2

theorem original_mass_stratum_count (K margin time H : Nat) :
    ((zeroSpatialPairs K margin time).filter (fun pair => decide (pairHigher margin pair = H))).length ≤
      replicaCapacity^H := by
  let pairs := (zeroSpatialPairs K margin time).filter (fun pair => decide (pairHigher margin pair = H))
  have hn := CayleyPruferInjection.nodup_map_of_injOn (profile margin) pairs
    ((zeroSpatialPairs_nodup K margin time).filter _)
    (fun a ha b hb he => profile_injective_on (List.mem_filter.mp ha).1 (List.mem_filter.mp hb).1 he)
  have hc := mass_stratum_count (2*(shortNearbyIds margin).length) H (pairs.map (profile margin)) hn
    (by intro values hv; obtain ⟨pair,_,rfl⟩ := List.mem_map.mp hv; exact profile_length margin pair)
    (by
      intro values hv
      obtain ⟨pair,hp,rfl⟩ := List.mem_map.mp hv
      obtain ⟨_,ids,hs,hm⟩ := zeroSpatialPairs_mem (List.mem_filter.mp hp).1
      exact (profile_mass hs hm).trans (of_decide_eq_true (List.mem_filter.mp hp).2))
  rw [List.length_map] at hc
  exact Nat.le_trans hc (Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 (shortNearbyIds_length_le margin)) H)

end YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount

#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount.flatten
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount.flatten_injective
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount.flatten_length
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount.flatten_mass
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount.profile
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount.profile_length
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount.profile_mass
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount.zeroSpatialKeep
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount.shortPairs
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount.zeroSpatialPairs
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount.zeroSpatialPairs_mem
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount.shortPairs_nodup
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount.zeroSpatialPairs_nodup
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount.profile_injective_on
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount.replicaCapacity
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount.zeroSpatialPairs_higher_positive
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount.original_mass_stratum_count
