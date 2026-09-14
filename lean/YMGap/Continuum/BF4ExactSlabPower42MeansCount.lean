/-
# At most four ORIGINAL power-42 means-channel short pairs

The common cap slice is an injective code for the actual original label
pair, including its zero nonphysical indices. The original short-pair
enumeration is duplicate free by selected-support uniqueness. Mapping
its nonzero power-42 means sector into range 4 therefore counts the
original multiplicities, without deduplicating or replacing the source.
-/

import YMGap.Continuum.BF4ExactSlabPower42MeansCaps

namespace YMGap.Continuum.BF4ExactSlabPower42MeansCount

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.BF4ExactSlabPower42MeansCaps
open YMGap.Continuum.BF4ExactSlabSpatialHeatPower42
open YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower
open YMGap.Continuum.BF4ExactSlabPairChannelParity
open YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction
open YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter
open YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit
open YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount
open YMGap.Continuum.BF4ExactSlabShortCoreHeatFactor
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

def means42Keep (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Bool :=
  decide (pairPower margin pair=42 ∧ ¬pairTerm margin pair.1 pair.2 ≈ 0 ∧
    spatialDefectKeep margin pair=true ∧ jointCheck margin pair=false)

def means42Pairs (K margin time : Nat) : List (EdgeLabelling × EdgeLabelling) :=
  (shortPairs K margin time).filter (means42Keep margin)

theorem means42_cap_pin {K margin time : Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hp : pair ∈ means42Pairs K margin time) :
    meansCapIndex margin pair < 4 ∧
      spatialOddFaces margin pair.1=[sliceFace margin (meansCapIndex margin pair)] ∧
      spatialOddFaces margin pair.2=[sliceFace margin (meansCapIndex margin pair)] := by
  have hk := of_decide_eq_true (List.mem_filter.mp hp).2
  obtain ⟨ids,hs,hm⟩ := List.mem_flatMap.mp (List.mem_filter.mp hp).1
  exact power42_means_four_slices (shortOtherCores_connected hs) hm hk.1 hk.2.1 hk.2.2.1 hk.2.2.2

theorem means42_fundamental {K margin time : Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hp : pair ∈ means42Pairs K margin time) (id : Nat)
    (hi : id ∈ slabPhysicalFaceEdges (responseExtent margin)) : pair.1 id ≤ 1 ∧ pair.2 id ≤ 1 := by
  have hk := of_decide_eq_true (List.mem_filter.mp hp).2
  obtain ⟨ids,hs,hm⟩ := List.mem_flatMap.mp (List.mem_filter.mp hp).1
  exact (retained_power42_fundamental (shortOtherCores_connected hs) hm hk.1).2 id hi

theorem means42_outside {K margin time : Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hp : pair ∈ means42Pairs K margin time) (id : Nat)
    (hi : id ∉ slabPhysicalFaceEdges (responseExtent margin)) : pair.1 id=0 ∧ pair.2 id=0 := by
  obtain ⟨ids,hs,hm⟩ := List.mem_flatMap.mp (List.mem_filter.mp hp).1
  have hc := shortOtherCores_connected hs
  exact outside K ids pair (List.mem_filter.mp (List.mem_filter.mp hm).1).1 id
    (fun hid => hi (selected_mem (List.mem_filter.mp hc).1 id hid))

theorem means42_checks {K margin time : Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hp : pair ∈ means42Pairs K margin time) :
    momentCheck margin true false pair.1=true ∧ momentCheck margin false true pair.2=true := by
  have hk := of_decide_eq_true (List.mem_filter.mp hp).2
  have hc := nonzero_pair_channel_checks margin pair hk.2.1
  simpa only [hk.2.2.2, Bool.not_false] using hc

theorem means42_code_injective {K margin time : Nat} {left right : EdgeLabelling × EdgeLabelling}
    (hl : left ∈ means42Pairs K margin time) (hr : right ∈ means42Pairs K margin time)
    (he : meansCapIndex margin left=meansCapIndex margin right) : left=right := by
  have hls := means42_cap_pin hl
  have hrs := means42_cap_pin hr
  have hspaceL := hls.2.1.trans ((congrArg (fun i => [sliceFace margin i]) he).trans hrs.2.1.symm)
  have hspaceR := hls.2.2.trans ((congrArg (fun i => [sliceFace margin i]) he).trans hrs.2.2.symm)
  have hlc := means42_checks hl
  have hrc := means42_checks hr
  have hphysical (id : Nat) (hi : id ∈ slabPhysicalFaceEdges (responseExtent margin)) :
      left.1 id=right.1 id ∧ left.2 id=right.2 id := by
    have h0 := spatial_odd_determine_face_parity margin true false left.1 right.1
      hlc.1 hrc.1 hspaceL (slabPlaquetteAt (responseExtent margin) id) (slabPlaquetteAt_mem hi)
    have h1 := spatial_odd_determine_face_parity margin false true left.2 right.2
      hlc.2 hrc.2 hspaceR (slabPlaquetteAt (responseExtent margin) id) (slabPlaquetteAt_mem hi)
    rw [idxOf_slabPlaquetteAt hi] at h0 h1
    have hbl := means42_fundamental hl id hi
    have hbr := means42_fundamental hr id hi
    constructor <;> omega
  apply Prod.ext
  · funext id
    by_cases hi : id ∈ slabPhysicalFaceEdges (responseExtent margin)
    · exact (hphysical id hi).1
    · exact (means42_outside hl id hi).1.trans (means42_outside hr id hi).1.symm
  · funext id
    by_cases hi : id ∈ slabPhysicalFaceEdges (responseExtent margin)
    · exact (hphysical id hi).2
    · exact (means42_outside hl id hi).2.trans (means42_outside hr id hi).2.symm

theorem original_means42_count (K margin time : Nat) : (means42Pairs K margin time).length ≤ 4 := by
  have hn := CayleyPruferInjection.nodup_map_of_injOn (meansCapIndex margin) (means42Pairs K margin time)
    ((shortPairs_nodup K margin time).filter _) (fun _ hl _ hr he => means42_code_injective hl hr he)
  have hc := CayleyPruferInjection.nodup_subset_length_le
    ((means42Pairs K margin time).map (meansCapIndex margin)) (List.range 4) hn (by
      intro i hi
      obtain ⟨pair,hp,rfl⟩ := List.mem_map.mp hi
      exact List.mem_range.mpr (means42_cap_pin hp).1)
  simpa only [List.length_map, List.length_range] using hc

end YMGap.Continuum.BF4ExactSlabPower42MeansCount

#print axioms YMGap.Continuum.BF4ExactSlabPower42MeansCount.means42Keep
#print axioms YMGap.Continuum.BF4ExactSlabPower42MeansCount.means42Pairs
#print axioms YMGap.Continuum.BF4ExactSlabPower42MeansCount.means42_cap_pin
#print axioms YMGap.Continuum.BF4ExactSlabPower42MeansCount.means42_fundamental
#print axioms YMGap.Continuum.BF4ExactSlabPower42MeansCount.means42_outside
#print axioms YMGap.Continuum.BF4ExactSlabPower42MeansCount.means42_checks
#print axioms YMGap.Continuum.BF4ExactSlabPower42MeansCount.means42_code_injective
#print axioms YMGap.Continuum.BF4ExactSlabPower42MeansCount.original_means42_count
