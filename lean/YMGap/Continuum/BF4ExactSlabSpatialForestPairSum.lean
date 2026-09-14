/-
# Sum every original remaining spatial forest with its higher-spin weights

The original (S,H) count and 12+S<=B+H occupation floor give two geometric
rates below one at the unchanged SU(2) nome 1/1024. The full absolute pair
sum is at most (1/16)*w^36, for every cutoff, margin and filter time.
This uses the actual configurations and original heat weights. Restoring
each OWN detached partition square is the next separate comparison.
-/

import YMGap.Continuum.BF4ExactSlabSpatialForestPairCount
import YMGap.Continuum.FiniteTwoSizeGeometricSum

namespace YMGap.Continuum.BF4ExactSlabSpatialForestPairSum

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.SU2FiniteHeatPowerFactorization
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2ParityHigherHeatEnvelope
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.FiniteTwoSizeGeometricSum
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.BF4ExactSlabSpatialForestPairCount
open YMGap.Continuum.BF4ExactSlabFourCapPairSum (original_spatial_occupation_floor)
open YMGap.Continuum.BF4ExactSlabTwoCapHeatBound
open YMGap.Continuum.BF4ExactSlabTwoCapPairSum (relative_entropy_guard)
open YMGap.Continuum.BF4ExactSlabParityHigherPairBound
open YMGap.Continuum.BF4ExactSlabPairChannelParity
open YMGap.Continuum.BF4ExactSlabShortCoreHeatFactor
open YMGap.Continuum.BF4ExactSlabShortCoreLocalization
open YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount (replicaCapacity)
open YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome)
open YMGap.Continuum.PairedPositiveFaceLabellings

local infix:50 " ≈ " => Q'.eqv

theorem spatial_entropy_guard : entropyRate 7200000 (oddRate nome) < 1 := by decide

theorem remaining_weight_bound {K margin time : Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hp : pair ∈ remainingPairs K margin time) :
    Q'.abs (weightedPairTerm nome K margin pair) ≤
      (8*qpow (oddRate nome) 12)*((oddRate nome)^(pairSpatial margin pair)*relativeHigherRate^(pairHigher margin pair)) := by
  obtain ⟨_,ids,hs,hm⟩ := remainingPairs_mem hp
  have hpair := (List.mem_filter.mp (List.mem_filter.mp hm).1).1
  have hb := weightedPairTerm_parity_bound (w := nome) (by decide) (by decide) K margin pair
    (fun id _ => bounded K ids pair hpair id)
  have hratio := ratio_power (oddRate nome) (higherRate nome) relativeHigherRate relativeHigher_pin
    (pairParity margin pair) (pairHigher margin pair)
  have hfloor := qpow_antitone (show (0 : Q') ≤ oddRate nome by decide) (by decide)
    (12+pairSpatial margin pair) _ (original_spatial_occupation_floor hs hm)
  have hraw : Q'.abs (weightedPairTerm nome K margin pair) ≤
      (8*qpow (oddRate nome) (12+pairSpatial margin pair))*relativeHigherRate^(pairHigher margin pair) :=
    Q'.le_trans' _ _ _ hb (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left 8 _ _ hratio)) (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ 8
          (Q'.mul_le_mul_of_nonneg_right _ _ _ hfloor (Q'.pow_nonneg _ relativeHigher_nonnegative _)) (by decide))
        (Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _))))
  have he : qpow (oddRate nome) (12+pairSpatial margin pair) ≈
      qpow (oddRate nome) 12*(oddRate nome)^(pairSpatial margin pair) :=
    Q'.eqv_trans _ _ _ (qpow_add (oddRate nome) 12 (pairSpatial margin pair))
      (Q'.mul_eqv_congr_left _ _ _ (qpow_to_pow _ _))
  apply Q'.le_trans' _ _ _ hraw
  apply Q'.le_of_eqv
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_left 8 _ _ he)) ?_
  exact poly_identity_of_normal_eq
    (.mul (.mul (.const 8) (.mul (.var 0) (.var 1))) (.var 2))
    (.mul (.mul (.const 8) (.var 0)) (.mul (.var 1) (.var 2))) (by decide)
    (fun i => if i=0 then qpow (oddRate nome) 12 else if i=1 then (oddRate nome)^(pairSpatial margin pair)
      else relativeHigherRate^(pairHigher margin pair))

theorem remaining_mass_sum (K margin time : Nat) :
    listQSum (fun pair => (oddRate nome)^(pairSpatial margin pair)*relativeHigherRate^(pairHigher margin pair))
      (remainingPairs K margin time) ≤
    twoMassBudget 7200000 replicaCapacity 6 (oddRate nome) relativeHigherRate
      spatial_entropy_guard relative_entropy_guard := by
  apply two_size_sum_bound _ (pairSpatial margin) (pairHigher margin) 7200000 replicaCapacity 6
    replicaCapacity (shortFaceCapacity*K) (by decide) relativeHigher_nonnegative
    spatial_entropy_guard relative_entropy_guard
  · exact fun _ hp => remaining_spatial_lower hp
  · exact fun _ hp => remaining_spatial_upper hp
  · exact fun _ hp => remaining_higher_upper hp
  · intro S H
    have he : ((remainingPairs K margin time).filter (fun pair => decide (S=pairSpatial margin pair))).filter
        (fun pair => decide (H=pairHigher margin pair)) =
        (remainingPairs K margin time).filter (fun pair => decide (pairSpatial margin pair=S ∧ pairHigher margin pair=H)) := by
      rw [List.filter_filter]
      apply List.filter_congr
      intro pair _
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true_iff,decide_eq_true_eq]
      constructor
      · exact fun h => ⟨h.2.symm,h.1.symm⟩
      · exact fun h => ⟨h.2.symm,h.1.symm⟩
    rw [he]
    exact original_remaining_mass_count K margin time S H

def remainingPairBudget : Q' := (8*qpow (oddRate nome) 12)*
  twoMassBudget 7200000 replicaCapacity 6 (oddRate nome) relativeHigherRate
    spatial_entropy_guard relative_entropy_guard

theorem original_remaining_pair_sum_bound (K margin time : Nat) :
    listQSum (fun pair => Q'.abs (weightedPairTerm nome K margin pair)) (remainingPairs K margin time) ≤
      remainingPairBudget := by
  have hb := sum_le_on _ _ (remainingPairs K margin time) (fun _ hp => remaining_weight_bound hp)
  exact Q'.le_trans' _ _ _ hb (Q'.le_trans' _ _ _ (Q'.le_of_eqv (listQSum_mul_left _ _ _))
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (remaining_mass_sum K margin time)
      (by decide : (0 : Q') ≤ 8*qpow (oddRate nome) 12)))

theorem remainingPairBudget_small : remainingPairBudget ≤ Q'.invSucc 15*qpow nome 36 := by decide

theorem original_remaining_pair_sum_small (K margin time : Nat) :
    listQSum (fun pair => Q'.abs (weightedPairTerm nome K margin pair)) (remainingPairs K margin time) ≤
      Q'.invSucc 15*qpow nome 36 :=
  Q'.le_trans' _ _ _ (original_remaining_pair_sum_bound K margin time) remainingPairBudget_small

end YMGap.Continuum.BF4ExactSlabSpatialForestPairSum

#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestPairSum.spatial_entropy_guard
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestPairSum.remaining_weight_bound
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestPairSum.remaining_mass_sum
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestPairSum.remainingPairBudget
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestPairSum.original_remaining_pair_sum_bound
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestPairSum.remainingPairBudget_small
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestPairSum.original_remaining_pair_sum_small
