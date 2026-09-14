/-
# Bound the whole original power-42 means-channel short remainder

There are at most four actual pairs, each with fourteen fundamental
occupations. The existing sharp character envelope gives a per-pair
bound 2^-29*w^36 at the unchanged nome 1/1024. The original pair sum is
therefore at most 2^-27*w^36. Restoring each core's OWN detached partition
square costs at most two, giving 2^-26*w^36*Z_full^2.

All K, volume margins and cut-filter times are explicit. This is not a
bound on the joint power-42 channel, higher powers or the whole response.
Scalar pilot: computations/original_power42_means_budget.py.
-/

import YMGap.Continuum.BF4ExactSlabPower42MeansCount
import YMGap.Continuum.BF4ExactSlabZeroSpatialRemainderBound

namespace YMGap.Continuum.BF4ExactSlabPower42MeansBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteParityHigherProduct
open YMGap.Continuum.SU2ParityHigherHeatEnvelope
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.BF4ExactSlabPower42MeansCount
open YMGap.Continuum.BF4ExactSlabSpatialHeatPower42
open YMGap.Continuum.BF4ExactSlabOddFaceIncidence
open YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction
open YMGap.Continuum.BF4ExactSlabMinimalPowerWindow (positive_eq_odd)
open YMGap.Continuum.BF4ExactSlabParityHigherPairBound
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow
open YMGap.Continuum.BF4ExactSlabShortCoreHeatFactor
open YMGap.Continuum.BF4ExactSlabShortSpatialRemainderSplit
open YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount
open YMGap.Continuum.BF4ExactSlabZeroSpatialRemainderBound
open YMGap.Continuum.BF4ExactSlabShortDetachedPartition
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome)
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

theorem higherCount_small_zero (state : Nat → Nat) : ∀ ids : List Nat,
    (∀ id, id ∈ ids → state id ≤ 1) → higherCount state ids=0
  | [], _ => rfl
  | id::ids, h => by
    have hb := h id List.mem_cons_self
    have ih := higherCount_small_zero state ids (fun i hi => h i (List.mem_cons_of_mem id hi))
    rw [higherCount, ih, Nat.div_eq_of_lt (by omega : state id < 2)]

theorem means42_heat_counts {K margin time : Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hp : pair ∈ means42Pairs K margin time) : pairParity margin pair=14 ∧ pairHigher margin pair=0 := by
  have hk := of_decide_eq_true (List.mem_filter.mp hp).2
  obtain ⟨ids,hs,hm⟩ := List.mem_flatMap.mp (List.mem_filter.mp hp).1
  have hf := retained_power42_fundamental (shortOtherCores_connected hs) hm hk.1
  constructor
  · have ha := hf.1
    rw [positive_eq_odd _ _ (fun id hi => (hf.2 id hi).1),
      positive_eq_odd _ _ (fun id hi => (hf.2 id hi).2), oddFaces_length, oddFaces_length] at ha
    exact ha
  · unfold pairHigher
    rw [higherCount_small_zero _ _ (fun id hi => (hf.2 id hi).1),
      higherCount_small_zero _ _ (fun id hi => (hf.2 id hi).2)]

def means42PairCap : Q' := Q'.invSucc (2^29-1)*qpow nome 36

def means42PairBudget : Q' := Q'.invSucc (2^27-1)*qpow nome 36

def means42Allowance : Q' := Q'.invSucc (2^26-1)*qpow nome 36

theorem means42_pair_bound {K margin time : Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hp : pair ∈ means42Pairs K margin time) :
    Q'.abs (weightedPairTerm nome K margin pair) ≤ means42PairCap := by
  have hc := means42_heat_counts hp
  obtain ⟨ids,_,hm⟩ := List.mem_flatMap.mp (List.mem_filter.mp hp).1
  have hb := weightedPairTerm_parity_bound (w := nome) (by decide) (by decide) K margin pair
    (fun id _ => bounded K ids pair (List.mem_filter.mp (List.mem_filter.mp hm).1).1 id)
  rw [hc.1,hc.2] at hb
  exact Q'.le_trans' _ _ _ hb (by decide :
    8*(qpow (oddRate nome) 14*qpow (higherRate nome) 0) ≤ means42PairCap)

theorem original_means42_pair_sum_bound (K margin time : Nat) :
    listQSum (fun pair => Q'.abs (weightedPairTerm nome K margin pair)) (means42Pairs K margin time) ≤
      means42PairBudget := by
  have hs := sum_le_on (fun pair => Q'.abs (weightedPairTerm nome K margin pair))
    (fun _ => means42PairCap) (means42Pairs K margin time) (fun _ hp => means42_pair_bound hp)
  have hc := Q'.mul_le_mul_of_nonneg_right _ _ means42PairCap
    (ClusterCount.ofNat_le_ofNat (original_means42_count K margin time)) (by decide)
  exact Q'.le_trans' _ _ _ hs (Q'.le_trans' _ _ _ (Q'.le_of_eqv (sum_const _ _))
    (Q'.le_trans' _ _ _ hc (by decide : Q'.ofNat 4*means42PairCap ≤ means42PairBudget)))

def means42Remainder (w : Q') (K margin time : Nat) : Q' :=
  branchRemainder w K margin time (means42Keep margin)

/-- The original signed subfamily retains every core-specific detached square. -/
theorem original_means42_remainder_bound (K margin time : Nat) :
    Q'.abs (means42Remainder nome K margin time) ≤
      means42Allowance*partitionSquare nome K (responseExtent margin)
        (slabPhysicalFaceEdges (responseExtent margin)) := by
  have h := signedFamily_abs_bound (shortOtherCores 33 margin)
    (fun ids => (corePairs K margin time ids).filter (means42Keep margin))
    (weightedPairTerm nome K margin) (detachedSquare nome K margin)
    (2*partitionSquare nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin)))
    (fun _ _ => SumOfSquares.q_mul_self_nonneg _)
    (fun _ hs => original_short_detached_square_le_two K margin hs)
  have ha : Q'.abs (means42Remainder nome K margin time) ≤
      listQSum (fun pair => Q'.abs (weightedPairTerm nome K margin pair)) (means42Pairs K margin time)*
        (2*partitionSquare nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin))) := by
    simpa only [means42Pairs, shortPairs, List.filter_flatMap, corePairs] using h
  have hb := Q'.mul_le_mul_of_nonneg_right _ _
    (2*partitionSquare nome K (responseExtent margin) (slabPhysicalFaceEdges (responseExtent margin)))
    (original_means42_pair_sum_bound K margin time)
    (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 2) (SumOfSquares.q_mul_self_nonneg _))
  have he (Z : Q') : means42PairBudget*(2*Z) ≈ means42Allowance*Z :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.mul_eqv_congr_right _ _ Z (by decide : means42PairBudget*2 ≈ means42Allowance))
  exact Q'.le_trans' _ _ _ ha (Q'.le_trans' _ _ _ hb (Q'.le_of_eqv (he _)))

end YMGap.Continuum.BF4ExactSlabPower42MeansBound

#print axioms YMGap.Continuum.BF4ExactSlabPower42MeansBound.higherCount_small_zero
#print axioms YMGap.Continuum.BF4ExactSlabPower42MeansBound.means42_heat_counts
#print axioms YMGap.Continuum.BF4ExactSlabPower42MeansBound.means42PairCap
#print axioms YMGap.Continuum.BF4ExactSlabPower42MeansBound.means42PairBudget
#print axioms YMGap.Continuum.BF4ExactSlabPower42MeansBound.means42Allowance
#print axioms YMGap.Continuum.BF4ExactSlabPower42MeansBound.means42_pair_bound
#print axioms YMGap.Continuum.BF4ExactSlabPower42MeansBound.original_means42_pair_sum_bound
#print axioms YMGap.Continuum.BF4ExactSlabPower42MeansBound.means42Remainder
#print axioms YMGap.Continuum.BF4ExactSlabPower42MeansBound.original_means42_remainder_bound
