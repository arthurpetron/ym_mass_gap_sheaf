/-
# Sum the complete original four-spatial-face family at fixed SU(2) nome

Twelve temporal occupations plus S spatial odd occurrences cost at least
12+S parity-plus-quotient units. For S=4 the original two-anchor count
therefore sums with the same relative higher rate 9/2^52. The actual
absolute pair sum is at most 2^-15*w^36 for every K, margin and filter time.
Detached partition comparison and the larger spatial families are separate.
-/

import YMGap.Continuum.BF4ExactSlabFourCapPairCount

namespace YMGap.Continuum.BF4ExactSlabFourCapPairSum

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2FiniteHeatPowerFactorization
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteParityHigherProduct
open YMGap.Continuum.SU2ParityHigherHeatEnvelope
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.BF4ExactSlabFourCapLocalCode (spatialCapacity)
open YMGap.Continuum.BF4ExactSlabFourCapPairCount
open YMGap.Continuum.BF4ExactSlabTwoCapHeatBound
open YMGap.Continuum.BF4ExactSlabTwoCapPairSum (relative_entropy_guard)
open YMGap.Continuum.BF4ExactSlabAfterMeansHeatPower48 (oddFaces_sublist_positive)
open YMGap.Continuum.BF4ExactSlabPower42SpatialBudget
open YMGap.Continuum.BF4ExactSlabParityHigherPairBound
open YMGap.Continuum.BF4ExactSlabPairChannelParity
open YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow
open YMGap.Continuum.BF4ExactSlabOriginalPairHeatPower
open YMGap.Continuum.BF4ExactSlabPositiveFaceCutMinimum (positiveFaces)
open YMGap.Continuum.BF4ExactSlabShortCoreHeatFactor
open YMGap.Continuum.BF4ExactSlabShortCoreLocalization
open YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount (replicaCapacity)
open YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome)
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4SpatialDefectTemporalDecoder (spatialFaces)

theorem original_spatial_positive_floor {K margin time : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling} (hs : ids ∈ shortOtherCores 33 margin)
    (hp : pair ∈ corePairs K margin time ids) :
    12+pairSpatial margin pair ≤
      (positiveFaces (responseExtent margin) pair.1).length+(positiveFaces (responseExtent margin) pair.2).length := by
  have hb := original_temporal_spatial_budget (shortOtherCores_connected hs) hp
  have hl := (List.Sublist.filter (fun face => decide ((dirsOf face.2).2 ≠ Dir4.x3))
    (oddFaces_sublist_positive (responseExtent margin) pair.1)).length_le
  have hr := (List.Sublist.filter (fun face => decide ((dirsOf face.2).2 ≠ Dir4.x3))
    (oddFaces_sublist_positive (responseExtent margin) pair.2)).length_le
  change (spatialOddFaces margin pair.1).length ≤ (spatialFaces (positiveFaces _ pair.1)).length at hl
  change (spatialOddFaces margin pair.2).length ≤ (spatialFaces (positiveFaces _ pair.2)).length at hr
  unfold pairSpatial
  omega

theorem original_spatial_occupation_floor {K margin time : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling} (hs : ids ∈ shortOtherCores 33 margin)
    (hp : pair ∈ corePairs K margin time ids) :
    12+pairSpatial margin pair ≤ pairParity margin pair+pairHigher margin pair := by
  have ha := original_spatial_positive_floor hs hp
  rw [positiveFaces_length,positiveFaces_length] at ha
  have hl := positiveCount_le_parity_higher pair.1 (slabPhysicalFaceEdges (responseExtent margin))
  have hr := positiveCount_le_parity_higher pair.2 (slabPhysicalFaceEdges (responseExtent margin))
  unfold pairParity pairHigher
  omega

theorem fourCap_weight_bound {K margin time : Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hp : pair ∈ fourCapPairs K margin time) :
    Q'.abs (weightedPairTerm nome K margin pair) ≤
      (8*qpow (oddRate nome) 16)*relativeHigherRate^(pairHigher margin pair) := by
  obtain ⟨hg,ids,hs,hm⟩ := fourCapPairs_mem hp
  have hpair := (List.mem_filter.mp (List.mem_filter.mp hm).1).1
  have hb := weightedPairTerm_parity_bound (w := nome) (by decide) (by decide) K margin pair
    (fun id _ => bounded K ids pair hpair id)
  have ha := original_spatial_occupation_floor hs hm
  rw [hg.1] at ha
  have hratio := ratio_power (oddRate nome) (higherRate nome) relativeHigherRate relativeHigher_pin
    (pairParity margin pair) (pairHigher margin pair)
  have hfloor := qpow_antitone (show (0 : Q') ≤ oddRate nome by decide) (by decide) 16 _ ha
  exact Q'.le_trans' _ _ _ hb (Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left 8 _ _ hratio)) (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ 8
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hfloor (Q'.pow_nonneg _ relativeHigher_nonnegative _)) (by decide))
      (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))))

theorem fourCap_mass_sum {r : Q'} (hr : (0 : Q') ≤ r)
    (hs : entropyRate replicaCapacity r < 1) (K margin time : Nat) :
    listQSum (fun pair => r^(pairHigher margin pair)) (fourCapPairs K margin time) ≤
      tailBudget spatialCapacity replicaCapacity 0 r hs := by
  apply size_sum_bound _ (pairHigher margin) spatialCapacity replicaCapacity 0
    (shortFaceCapacity*K) hr hs
  · intro pair _; exact Nat.zero_le _
  · intro pair hp; exact fourCap_higher_upper hp
  · intro H
    have he : (fourCapPairs K margin time).filter (fun pair => decide (H=pairHigher margin pair))=
        (fourCapPairs K margin time).filter (fun pair => decide (pairHigher margin pair=H)) := by
      apply List.filter_congr
      intro pair _
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      exact eq_comm
    rw [he]
    exact original_fourCap_mass_count K margin time H

def fourCapPairBudget : Q' :=
  (8*qpow (oddRate nome) 16)*tailBudget spatialCapacity replicaCapacity 0 relativeHigherRate relative_entropy_guard

theorem original_fourCap_pair_sum_bound (K margin time : Nat) :
    listQSum (fun pair => Q'.abs (weightedPairTerm nome K margin pair)) (fourCapPairs K margin time) ≤
      fourCapPairBudget := by
  have hb := sum_le_on (fun pair => Q'.abs (weightedPairTerm nome K margin pair))
    (fun pair => (8*qpow (oddRate nome) 16)*relativeHigherRate^(pairHigher margin pair))
    (fourCapPairs K margin time) (fun _ hp => fourCap_weight_bound hp)
  exact Q'.le_trans' _ _ _ hb (Q'.le_trans' _ _ _ (Q'.le_of_eqv (listQSum_mul_left _ _ _))
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (fourCap_mass_sum relativeHigher_nonnegative relative_entropy_guard K margin time)
      (by decide : (0 : Q') ≤ 8*qpow (oddRate nome) 16)))

theorem fourCapPairBudget_small : fourCapPairBudget ≤ Q'.invSucc (2^15-1)*qpow nome 36 := by decide

theorem original_fourCap_pair_sum_small (K margin time : Nat) :
    listQSum (fun pair => Q'.abs (weightedPairTerm nome K margin pair)) (fourCapPairs K margin time) ≤
      Q'.invSucc (2^15-1)*qpow nome 36 :=
  Q'.le_trans' _ _ _ (original_fourCap_pair_sum_bound K margin time) fourCapPairBudget_small

end YMGap.Continuum.BF4ExactSlabFourCapPairSum

#print axioms YMGap.Continuum.BF4ExactSlabFourCapPairSum.original_spatial_positive_floor
#print axioms YMGap.Continuum.BF4ExactSlabFourCapPairSum.original_spatial_occupation_floor
#print axioms YMGap.Continuum.BF4ExactSlabFourCapPairSum.fourCap_weight_bound
#print axioms YMGap.Continuum.BF4ExactSlabFourCapPairSum.fourCap_mass_sum
#print axioms YMGap.Continuum.BF4ExactSlabFourCapPairSum.fourCapPairBudget
#print axioms YMGap.Continuum.BF4ExactSlabFourCapPairSum.original_fourCap_pair_sum_bound
#print axioms YMGap.Continuum.BF4ExactSlabFourCapPairSum.fourCapPairBudget_small
#print axioms YMGap.Continuum.BF4ExactSlabFourCapPairSum.original_fourCap_pair_sum_small
