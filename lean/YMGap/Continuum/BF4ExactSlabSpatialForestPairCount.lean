/-
# Count every original remaining spatial forest and every higher-spin label

The actual short-core pairs surviving the four-face extraction are injected
into a whole-forest code and a higher-label unit word. At spatial mass S and
quotient mass H their count is at most 7200000^S * replicaCapacity^H,
independently of cutoff, margin and cut-filter time. Both replica tags and
the full original plaquettes are retained. No source is deduplicated.

This is the full two-mass configuration count, not yet its weighted sum or
the signed-remainder absorption. Terms removed by remainingKeep have zero
pairTerm or fail the existing afterFourCapKeep predicate.
-/

import YMGap.Continuum.BF4ExactSlabSpatialForestRecovery
import YMGap.Continuum.BF4ExactSlabAfterFourCapRemainder

namespace YMGap.Continuum.BF4ExactSlabSpatialForestPairCount

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.FiniteOccupationUnitCode
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.BF4ExactSlabSpatialForestCode
open YMGap.Continuum.BF4ExactSlabSpatialForestRecovery
open YMGap.Continuum.BF4ExactSlabSpatialComponentAnimal
open YMGap.Continuum.BF4ExactSlabSpatialOccurrenceNeighbors
open YMGap.Continuum.BF4ExactSlabLocalOccurrenceLattice
open YMGap.Continuum.BF4ExactSlabTwoCapLocalCode (cartesian_length)
open YMGap.Continuum.BF4ExactSlabTwoCapPairCount (spatial_higherCode_injective)
open YMGap.Continuum.BF4ExactSlabAfterFourCapRemainder
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
local instance : DecidableEq Z4Plaq := inferInstanceAs (DecidableEq (Z4Vertex × Z4Plane))

def remainingKeep (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Bool :=
  decide (¬pairTerm margin pair.1 pair.2 ≈ 0 ∧ afterFourCapKeep margin pair=true)

def remainingPairs (K margin time : Nat) : List (EdgeLabelling × EdgeLabelling) :=
  (shortPairs K margin time).filter (remainingKeep margin)

theorem remainingPairs_mem {K margin time : Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hp : pair ∈ remainingPairs K margin time) :
    (¬pairTerm margin pair.1 pair.2 ≈ 0 ∧ afterFourCapKeep margin pair=true) ∧
      ∃ ids, ids ∈ shortOtherCores 33 margin ∧ pair ∈ corePairs K margin time ids := by
  have hk := of_decide_eq_true (List.mem_filter.mp hp).2
  obtain ⟨ids,hs,hm⟩ := List.mem_flatMap.mp (List.mem_filter.mp hp).1
  exact ⟨hk,ids,hs,hm⟩

def pairCode (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) :=
  (code margin pair,unitWord (profile margin pair))

theorem pairCode_spatial_eq {margin : Nat} {left right : EdgeLabelling × EdgeLabelling}
    (he : pairCode margin left=pairCode margin right) : code margin left=code margin right :=
  (Prod.mk.inj he).1

theorem pairCode_higher_eq {margin : Nat} {left right : EdgeLabelling × EdgeLabelling}
    (he : pairCode margin left=pairCode margin right) : higherCode margin left=higherCode margin right := by
  have hh := unitWord_injective (profile margin left) (profile margin right)
    ((profile_length margin left).trans (profile_length margin right).symm) (congrArg Prod.snd he)
  exact flatten_injective _ _ hh

theorem pairCode_injective {K margin time : Nat} {left right : EdgeLabelling × EdgeLabelling}
    (hl : left ∈ remainingPairs K margin time) (hr : right ∈ remainingPairs K margin time)
    (he : pairCode margin left=pairCode margin right) : left=right := by
  obtain ⟨hlc,leftIds,hls,hlp⟩ := remainingPairs_mem hl
  obtain ⟨hrc,rightIds,hrs,hrp⟩ := remainingPairs_mem hr
  have hlp' := (List.mem_filter.mp (List.mem_filter.mp hlp).1).1
  have hrp' := (List.mem_filter.mp (List.mem_filter.mp hrp).1).1
  have hs := code_recover_spatial (margin := margin) (left := left) (right := right)
    (short_locality hls hlp') (short_locality hrs hrp') (pairCode_spatial_eq he)
  exact spatial_higherCode_injective hls hrs hlp' hrp' hlc.1 hrc.1 hs.1 hs.2
    (pairCode_higher_eq he)

theorem remaining_spatial_lower {K margin time : Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hp : pair ∈ remainingPairs K margin time) : 6 ≤ pairSpatial margin pair := by
  have hg := (remainingPairs_mem hp).1
  exact afterFourCap_spatial_minimum_six margin pair hg.1 hg.2

theorem remaining_spatial_upper {K margin time : Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hp : pair ∈ remainingPairs K margin time) : pairSpatial margin pair ≤ replicaCapacity := by
  obtain ⟨_,ids,hs,hm⟩ := remainingPairs_mem hp
  have hm' := (List.mem_filter.mp (List.mem_filter.mp hm).1).1
  have hc := nodup_subset_length_le (occurrences margin pair) (rootCarrier margin)
    (occurrences_nodup margin pair) (short_locality hs hm')
  rw [occurrences_length] at hc
  exact Nat.le_trans hc (rootCarrier_length_le margin)

theorem remaining_higher_upper {K margin time : Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hp : pair ∈ remainingPairs K margin time) : pairHigher margin pair ≤ shortFaceCapacity*K := by
  obtain ⟨_,ids,hs,hp⟩ := remainingPairs_mem hp
  have hm := (List.mem_filter.mp (List.mem_filter.mp hp).1).1
  have hc := codeHigher_bound K (higherCode margin pair) (by
    intro entry he
    have hb := higherCode_bounded hm entry he
    omega)
  rw [higherCode_power hs hm] at hc
  exact Nat.le_trans hc (Nat.mul_le_mul_right K (higherCode_length_le margin pair))

theorem original_remaining_mass_count (K margin time S H : Nat) :
    ((remainingPairs K margin time).filter (fun pair =>
      decide (pairSpatial margin pair=S ∧ pairHigher margin pair=H))).length ≤
      7200000^S*replicaCapacity^H := by
  let pairs := (remainingPairs K margin time).filter (fun pair =>
    decide (pairSpatial margin pair=S ∧ pairHigher margin pair=H))
  have hn := nodup_map_of_injOn (pairCode margin) pairs (((shortPairs_nodup K margin time).filter _).filter _)
    (fun a ha b hb he => pairCode_injective (List.mem_filter.mp ha).1 (List.mem_filter.mp hb).1 he)
  have hc := nodup_subset_length_le (pairs.map (pairCode margin))
    (cartesian (codeCarrier margin S) (allSeqs replicaCapacity H)) hn (by
      intro code hcode
      obtain ⟨pair,hp,rfl⟩ := List.mem_map.mp hcode
      obtain ⟨hguard,ids,hs,hm⟩ := remainingPairs_mem (List.mem_filter.mp hp).1
      have hm' := (List.mem_filter.mp (List.mem_filter.mp hm).1).1
      have hmass := of_decide_eq_true (List.mem_filter.mp hp).2
      apply (mem_cartesian_iff _ _ _).mpr
      constructor
      · rw [← hmass.1]
        exact code_mem margin pair (short_locality hs hm') hguard.1
      · apply unitWord_mem replicaCapacity H (profile margin pair)
        · rw [profile_length]
          exact Nat.mul_le_mul_left 2 (shortNearbyIds_length_le margin)
        · exact (profile_mass hs hm').trans hmass.2)
  rw [List.length_map,cartesian_length,length_allSeqs] at hc
  exact Nat.le_trans hc (Nat.mul_le_mul_right (replicaCapacity^H) (codeCarrier_length_le margin S))

end YMGap.Continuum.BF4ExactSlabSpatialForestPairCount

#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestPairCount.remainingKeep
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestPairCount.remainingPairs
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestPairCount.remainingPairs_mem
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestPairCount.pairCode
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestPairCount.pairCode_spatial_eq
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestPairCount.pairCode_higher_eq
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestPairCount.pairCode_injective
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestPairCount.remaining_spatial_lower
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestPairCount.remaining_spatial_upper
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestPairCount.remaining_higher_upper
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestPairCount.original_remaining_mass_count
