/-
# Count the ORIGINAL remaining two-cap pairs by higher-label mass

The source is the literal short-pair enumeration after means-42 removal,
restricted to two spatial odd faces and nonzero original connected term.
The spatial cap code plus the local higher-label profile recovers the
ENTIRE original pair, including nonphysical indices. Unit words count
mass-H profiles without a cutoff factor. Thus the original H-stratum has
at most spatialCapacity*replicaCapacity^H members. No source is deduplicated.
-/

import YMGap.Continuum.BF4ExactSlabTwoCapLocalCode
import YMGap.Continuum.BF4ExactSlabAfterMeansHeatPower48

namespace YMGap.Continuum.BF4ExactSlabTwoCapPairCount

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.FiniteOccupationUnitCode
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.BF4ExactSlabTwoCapSpatialCode
open YMGap.Continuum.BF4ExactSlabTwoCapLocalCode
open YMGap.Continuum.BF4ExactSlabAfterMeans42Remainder
open YMGap.Continuum.BF4ExactSlabShortCoreLocalization
open YMGap.Continuum.BF4ExactSlabLocalizedHigherCode
open YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount
open YMGap.Continuum.BF4ExactSlabZeroSpatialPairSum (codeHigher_bound)
open YMGap.Continuum.BF4ExactSlabParityHigherPairBound
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow
open YMGap.Continuum.BF4ExactSlabPairChannelParity
open YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction
open YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

def twoCapKeep (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Bool :=
  decide (pairSpatial margin pair=2 ∧ ¬pairTerm margin pair.1 pair.2 ≈ 0 ∧ afterMeans42Keep margin pair=true)

def twoCapPairs (K margin time : Nat) : List (EdgeLabelling × EdgeLabelling) :=
  (shortPairs K margin time).filter (twoCapKeep margin)

theorem twoCapPairs_mem {K margin time : Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hp : pair ∈ twoCapPairs K margin time) :
    (pairSpatial margin pair=2 ∧ ¬pairTerm margin pair.1 pair.2 ≈ 0 ∧ afterMeans42Keep margin pair=true) ∧
      ∃ ids, ids ∈ shortOtherCores 33 margin ∧ pair ∈ corePairs K margin time ids := by
  have hk := of_decide_eq_true (List.mem_filter.mp hp).2
  obtain ⟨ids,hs,hm⟩ := List.mem_flatMap.mp (List.mem_filter.mp hp).1
  exact ⟨hk,ids,hs,hm⟩

/-- General original reconstruction; the spatial lists need not be empty. -/
theorem spatial_higherCode_injective {K margin : Nat} {leftIds rightIds : List Nat}
    {left right : EdgeLabelling × EdgeLabelling}
    (hls : leftIds ∈ shortOtherCores 33 margin) (hrs : rightIds ∈ shortOtherCores 33 margin)
    (hlp : left ∈ labels K leftIds) (hrp : right ∈ labels K rightIds)
    (hln : ¬pairTerm margin left.1 left.2 ≈ 0) (hrn : ¬pairTerm margin right.1 right.2 ≈ 0)
    (hs0 : spatialOddFaces margin left.1=spatialOddFaces margin right.1)
    (hs1 : spatialOddFaces margin left.2=spatialOddFaces margin right.2)
    (he : higherCode margin left=higherCode margin right) : left=right := by
  have hlc := nonzero_pair_channel_checks margin left hln
  have hrc := nonzero_pair_channel_checks margin right hrn
  have hchan := channel_eq_of_spatial_eq hln hrn hs0
  rw [hchan] at hlc
  have hq (id : Nat) (hi : id ∈ shortNearbyIds margin) :
      (left.1 id/2,left.2 id/2)=(right.1 id/2,right.2 id/2) := map_equal_on _ _ _ he id hi
  apply Prod.ext
  · funext id
    by_cases hi : id ∈ shortNearbyIds margin
    · have hphys := nearbyIds_physical hi
      have h := spatial_and_higher_determine_face_label margin true (jointCheck margin right)
        left.1 right.1 hlc.1 hrc.1 hs0 _ (slabPlaquetteAt_mem hphys)
        (by rw [idxOf_slabPlaquetteAt hphys]; exact congrArg Prod.fst (hq id hi))
      rw [idxOf_slabPlaquetteAt hphys] at h
      exact h
    · exact (short_pair_outside hls hlp id hi).1.trans (short_pair_outside hrs hrp id hi).1.symm
  · funext id
    by_cases hi : id ∈ shortNearbyIds margin
    · have hphys := nearbyIds_physical hi
      have h := spatial_and_higher_determine_face_label margin false (!(jointCheck margin right))
        left.2 right.2 hlc.2 hrc.2 hs1 _ (slabPlaquetteAt_mem hphys)
        (by rw [idxOf_slabPlaquetteAt hphys]; exact congrArg Prod.snd (hq id hi))
      rw [idxOf_slabPlaquetteAt hphys] at h
      exact h
    · exact (short_pair_outside hls hlp id hi).2.trans (short_pair_outside hrs hrp id hi).2.symm

def pairCode (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) :=
  (capCode margin pair,unitWord (profile margin pair))

theorem pairCode_injective {K margin time : Nat} {left right : EdgeLabelling × EdgeLabelling}
    (hl : left ∈ twoCapPairs K margin time) (hr : right ∈ twoCapPairs K margin time)
    (he : pairCode margin left=pairCode margin right) : left=right := by
  obtain ⟨hlc,leftIds,hls,hlp⟩ := twoCapPairs_mem hl
  obtain ⟨hrc,rightIds,hrs,hrp⟩ := twoCapPairs_mem hr
  have hlp' := (List.mem_filter.mp (List.mem_filter.mp hlp).1).1
  have hrp' := (List.mem_filter.mp (List.mem_filter.mp hrp).1).1
  have hs := capCode_recover_spatial hls hrs hlp' hrp' hlc.2.1 hrc.2.1 hlc.1 hrc.1
    (congrArg Prod.fst he)
  have hh := unitWord_injective (profile margin left) (profile margin right)
    ((profile_length margin left).trans (profile_length margin right).symm) (congrArg Prod.snd he)
  exact spatial_higherCode_injective hls hrs hlp' hrp' hlc.2.1 hrc.2.1 hs.1 hs.2
    (flatten_injective _ _ hh)

theorem twoCap_higher_upper {K margin time : Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hp : pair ∈ twoCapPairs K margin time) : pairHigher margin pair ≤ shortFaceCapacity*K := by
  obtain ⟨_,ids,hs,hp⟩ := twoCapPairs_mem hp
  have hm := (List.mem_filter.mp (List.mem_filter.mp hp).1).1
  have hc := codeHigher_bound K (higherCode margin pair) (by
    intro entry he
    have hb := higherCode_bounded hm entry he
    omega)
  rw [higherCode_power hs hm] at hc
  exact Nat.le_trans hc (Nat.mul_le_mul_right K (higherCode_length_le margin pair))

theorem original_twoCap_mass_count (K margin time H : Nat) :
    ((twoCapPairs K margin time).filter (fun pair => decide (pairHigher margin pair=H))).length ≤
      spatialCapacity*replicaCapacity^H := by
  letI : DecidableEq Z4Plaq := inferInstanceAs (DecidableEq (Z4Vertex × Z4Plane))
  let pairs := (twoCapPairs K margin time).filter (fun pair => decide (pairHigher margin pair=H))
  have hn := nodup_map_of_injOn (pairCode margin) pairs (((shortPairs_nodup K margin time).filter _).filter _)
    (fun a ha b hb he => pairCode_injective (List.mem_filter.mp ha).1 (List.mem_filter.mp hb).1 he)
  have hc := nodup_subset_length_le (pairs.map (pairCode margin))
    (cartesian (capCodes margin) (allSeqs replicaCapacity H)) hn (by
      intro code hcode
      obtain ⟨pair,hp,rfl⟩ := List.mem_map.mp hcode
      obtain ⟨hguard,ids,hs,hm⟩ := twoCapPairs_mem (List.mem_filter.mp hp).1
      have hm' := (List.mem_filter.mp (List.mem_filter.mp hm).1).1
      apply (mem_cartesian_iff _ _ _).mpr
      constructor
      · exact capCode_mem hs hm' hguard.1
      · apply unitWord_mem replicaCapacity H (profile margin pair)
        · rw [profile_length]
          exact Nat.mul_le_mul_left 2 (shortNearbyIds_length_le margin)
        · exact (profile_mass hs hm').trans (of_decide_eq_true (List.mem_filter.mp hp).2))
  rw [List.length_map,cartesian_length,length_allSeqs] at hc
  exact Nat.le_trans hc (Nat.mul_le_mul_right (replicaCapacity^H) (capCodes_length_le margin))

end YMGap.Continuum.BF4ExactSlabTwoCapPairCount

#print axioms YMGap.Continuum.BF4ExactSlabTwoCapPairCount.twoCapKeep
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapPairCount.twoCapPairs
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapPairCount.twoCapPairs_mem
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapPairCount.spatial_higherCode_injective
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapPairCount.pairCode
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapPairCount.pairCode_injective
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapPairCount.twoCap_higher_upper
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapPairCount.original_twoCap_mass_count
