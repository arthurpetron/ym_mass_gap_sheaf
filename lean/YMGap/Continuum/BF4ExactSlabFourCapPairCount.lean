/-
# Count the original four-spatial-face family, including all higher spins

The computed two-anchor code and a higher-label unit word inject the
literal remaining four-face pairs into a finite product. No source is
deduplicated. At quotient mass H the count is at most
(5*3*shortFaceCapacity^2*67^2)*replicaCapacity^H, uniformly in cutoff,
margin and cut-filter time. The original weights are not replaced.
-/

import YMGap.Continuum.BF4ExactSlabFourCapLocalCode
import YMGap.Continuum.BF4ExactSlabAfterTwoCapRemainder

namespace YMGap.Continuum.BF4ExactSlabFourCapPairCount

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.FiniteOccupationUnitCode
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.BF4ExactSlabFourCapLocalCode
open YMGap.Continuum.BF4ExactSlabTwoCapLocalCode (cartesian_length)
open YMGap.Continuum.BF4ExactSlabTwoCapPairCount (spatial_higherCode_injective)
open YMGap.Continuum.BF4ExactSlabAfterTwoCapRemainder
open YMGap.Continuum.BF4ExactSlabShortCoreLocalization
open YMGap.Continuum.BF4ExactSlabLocalizedHigherCode
open YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount
open YMGap.Continuum.BF4ExactSlabZeroSpatialPairSum (codeHigher_bound)
open YMGap.Continuum.BF4ExactSlabParityHigherPairBound
open YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow
open YMGap.Continuum.BF4ExactSlabPairChannelParity
open YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.PairedPositiveFaceLabellings

local infix:50 " ≈ " => Q'.eqv

def fourCapKeep (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Bool :=
  decide (pairSpatial margin pair=4 ∧ ¬pairTerm margin pair.1 pair.2 ≈ 0 ∧ afterTwoCapKeep margin pair=true)

def fourCapPairs (K margin time : Nat) : List (EdgeLabelling × EdgeLabelling) :=
  (shortPairs K margin time).filter (fourCapKeep margin)

theorem fourCapPairs_mem {K margin time : Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hp : pair ∈ fourCapPairs K margin time) :
    (pairSpatial margin pair=4 ∧ ¬pairTerm margin pair.1 pair.2 ≈ 0 ∧ afterTwoCapKeep margin pair=true) ∧
      ∃ ids, ids ∈ shortOtherCores 33 margin ∧ pair ∈ corePairs K margin time ids := by
  have hk := of_decide_eq_true (List.mem_filter.mp hp).2
  obtain ⟨ids,hs,hm⟩ := List.mem_flatMap.mp (List.mem_filter.mp hp).1
  exact ⟨hk,ids,hs,hm⟩

def pairCode (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) :=
  (code margin pair,unitWord (profile margin pair))

theorem pairCode_injective {K margin time : Nat} {left right : EdgeLabelling × EdgeLabelling}
    (hl : left ∈ fourCapPairs K margin time) (hr : right ∈ fourCapPairs K margin time)
    (he : pairCode margin left=pairCode margin right) : left=right := by
  obtain ⟨hlc,leftIds,hls,hlp⟩ := fourCapPairs_mem hl
  obtain ⟨hrc,rightIds,hrs,hrp⟩ := fourCapPairs_mem hr
  have hlp' := (List.mem_filter.mp (List.mem_filter.mp hlp).1).1
  have hrp' := (List.mem_filter.mp (List.mem_filter.mp hrp).1).1
  have hs := code_recover_spatial hls hrs hlp' hrp' hlc.2.1 hrc.2.1 hlc.1 hrc.1
    (congrArg Prod.fst he)
  have hh := unitWord_injective (profile margin left) (profile margin right)
    ((profile_length margin left).trans (profile_length margin right).symm) (congrArg Prod.snd he)
  exact spatial_higherCode_injective hls hrs hlp' hrp' hlc.2.1 hrc.2.1 hs.1 hs.2
    (flatten_injective _ _ hh)

theorem fourCap_higher_upper {K margin time : Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hp : pair ∈ fourCapPairs K margin time) : pairHigher margin pair ≤ shortFaceCapacity*K := by
  obtain ⟨_,ids,hs,hp⟩ := fourCapPairs_mem hp
  have hm := (List.mem_filter.mp (List.mem_filter.mp hp).1).1
  have hc := codeHigher_bound K (higherCode margin pair) (by
    intro entry he
    have hb := higherCode_bounded hm entry he
    omega)
  rw [higherCode_power hs hm] at hc
  exact Nat.le_trans hc (Nat.mul_le_mul_right K (higherCode_length_le margin pair))

theorem original_fourCap_mass_count (K margin time H : Nat) :
    ((fourCapPairs K margin time).filter (fun pair => decide (pairHigher margin pair=H))).length ≤
      spatialCapacity*replicaCapacity^H := by
  letI : DecidableEq Z4Plaq := inferInstanceAs (DecidableEq (Z4Vertex × Z4Plane))
  letI : DecidableEq Z4FourProjectedFaceCode.Code :=
    inferInstanceAs (DecidableEq (Nat × Z4Plaq × Z4Plaq × Nat × Nat))
  let pairs := (fourCapPairs K margin time).filter (fun pair => decide (pairHigher margin pair=H))
  have hn := nodup_map_of_injOn (pairCode margin) pairs (((shortPairs_nodup K margin time).filter _).filter _)
    (fun a ha b hb he => pairCode_injective (List.mem_filter.mp ha).1 (List.mem_filter.mp hb).1 he)
  have hc := nodup_subset_length_le (pairs.map (pairCode margin))
    (cartesian (codes margin) (allSeqs replicaCapacity H)) hn (by
      intro code hcode
      obtain ⟨pair,hp,rfl⟩ := List.mem_map.mp hcode
      obtain ⟨hguard,ids,hs,hm⟩ := fourCapPairs_mem (List.mem_filter.mp hp).1
      have hm' := (List.mem_filter.mp (List.mem_filter.mp hm).1).1
      apply (mem_cartesian_iff _ _ _).mpr
      constructor
      · exact code_mem hs hm' hguard.1
      · apply unitWord_mem replicaCapacity H (profile margin pair)
        · rw [profile_length]
          exact Nat.mul_le_mul_left 2 (shortNearbyIds_length_le margin)
        · exact (profile_mass hs hm').trans (of_decide_eq_true (List.mem_filter.mp hp).2))
  rw [List.length_map,cartesian_length,length_allSeqs] at hc
  exact Nat.le_trans hc (Nat.mul_le_mul_right (replicaCapacity^H) (codes_length_le margin))

end YMGap.Continuum.BF4ExactSlabFourCapPairCount

#print axioms YMGap.Continuum.BF4ExactSlabFourCapPairCount.fourCapKeep
#print axioms YMGap.Continuum.BF4ExactSlabFourCapPairCount.fourCapPairs
#print axioms YMGap.Continuum.BF4ExactSlabFourCapPairCount.fourCapPairs_mem
#print axioms YMGap.Continuum.BF4ExactSlabFourCapPairCount.pairCode
#print axioms YMGap.Continuum.BF4ExactSlabFourCapPairCount.pairCode_injective
#print axioms YMGap.Continuum.BF4ExactSlabFourCapPairCount.fourCap_higher_upper
#print axioms YMGap.Continuum.BF4ExactSlabFourCapPairCount.original_fourCap_mass_count
