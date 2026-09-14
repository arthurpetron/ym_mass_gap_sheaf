/-
# Sum the ORIGINAL remaining two-cap family at every cutoff and volume

Zero higher mass uses the sixteen-parity-bit floor. Positive higher mass
uses the fourteen-occupation floor and the explicit relative rate 9/2^52.
The proved original mass-stratum count gives one finite geometric tail,
with no cutoff or volume factor. At nome 1/1024 the total absolute pair
sum is at most 2^-15*w^36. Detached partitions are handled downstream.
-/

import YMGap.Continuum.BF4ExactSlabTwoCapHeatBound

namespace YMGap.Continuum.BF4ExactSlabTwoCapPairSum

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.Z4CanonicalPolymerRange (listQSum_perm)
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2ParityHigherHeatEnvelope
open YMGap.Continuum.BF4ExactSlabTwoCapLocalCode
open YMGap.Continuum.BF4ExactSlabTwoCapPairCount
open YMGap.Continuum.BF4ExactSlabTwoCapHeatBound
open YMGap.Continuum.BF4ExactSlabShortCoreLocalization
open YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount (replicaCapacity)
open YMGap.Continuum.BF4ExactSlabParityHigherPairBound
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome)

local infix:50 " ≈ " => Q'.eqv

def fundamentalPairs (K margin time : Nat) : List (EdgeLabelling × EdgeLabelling) :=
  (twoCapPairs K margin time).filter (fun pair => decide (pairHigher margin pair=0))

def higherPairs (K margin time : Nat) : List (EdgeLabelling × EdgeLabelling) :=
  (twoCapPairs K margin time).filter (fun pair => !decide (pairHigher margin pair=0))

theorem fundamental_count (K margin time : Nat) : (fundamentalPairs K margin time).length ≤ spatialCapacity := by
  have hc := original_twoCap_mass_count K margin time 0
  simpa only [Nat.pow_zero,Nat.mul_one] using hc

theorem fundamental_weight_sum (K margin time : Nat) :
    listQSum (fun pair => Q'.abs (weightedPairTerm nome K margin pair)) (fundamentalPairs K margin time) ≤
      Q'.ofNat spatialCapacity*(8*qpow (oddRate nome) 16) := by
  have hb := sum_le_on (fun pair => Q'.abs (weightedPairTerm nome K margin pair))
    (fun _ => 8*qpow (oddRate nome) 16) (fundamentalPairs K margin time)
    (fun _ hp => twoCap_fundamental_weight_bound (List.mem_filter.mp hp).1
      (of_decide_eq_true (List.mem_filter.mp hp).2))
  exact Q'.le_trans' _ _ _ hb (Q'.le_trans' _ _ _ (Q'.le_of_eqv (sum_const _ _))
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (ClusterCount.ofNat_le_ofNat (fundamental_count K margin time))
      (by decide : (0 : Q') ≤ 8*qpow (oddRate nome) 16)))

theorem higher_mass_sum {r : Q'} (hr : (0 : Q') ≤ r)
    (hs : entropyRate replicaCapacity r < 1) (K margin time : Nat) :
    listQSum (fun pair => r^(pairHigher margin pair)) (higherPairs K margin time) ≤
      tailBudget spatialCapacity replicaCapacity 1 r hs := by
  apply size_sum_bound _ (pairHigher margin) spatialCapacity replicaCapacity 1
    (shortFaceCapacity*K) hr hs
  · intro pair hp
    have hn : ¬pairHigher margin pair=0 := by
      simpa only [Bool.not_eq_true',decide_eq_false_iff_not] using (List.mem_filter.mp hp).2
    omega
  · intro pair hp
    exact twoCap_higher_upper (List.mem_filter.mp hp).1
  · intro H
    have hsub : ((higherPairs K margin time).filter (fun pair => decide (H=pairHigher margin pair))).Sublist
        ((twoCapPairs K margin time).filter (fun pair => decide (H=pairHigher margin pair))) :=
      List.Sublist.filter _ List.filter_sublist
    have he : (twoCapPairs K margin time).filter (fun pair => decide (H=pairHigher margin pair))=
        (twoCapPairs K margin time).filter (fun pair => decide (pairHigher margin pair=H)) := by
      apply List.filter_congr
      intro pair _
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      exact eq_comm
    have hc := hsub.length_le
    rw [he] at hc
    exact Nat.le_trans hc (original_twoCap_mass_count K margin time H)

theorem relative_entropy_guard : entropyRate replicaCapacity relativeHigherRate < 1 := by decide

theorem higher_weight_sum (K margin time : Nat) :
    listQSum (fun pair => Q'.abs (weightedPairTerm nome K margin pair)) (higherPairs K margin time) ≤
      (8*qpow (oddRate nome) 14)*tailBudget spatialCapacity replicaCapacity 1 relativeHigherRate relative_entropy_guard := by
  have hb := sum_le_on (fun pair => Q'.abs (weightedPairTerm nome K margin pair))
    (fun pair => (8*qpow (oddRate nome) 14)*relativeHigherRate^(pairHigher margin pair))
    (higherPairs K margin time) (fun _ hp => twoCap_weight_bound (List.mem_filter.mp hp).1)
  exact Q'.le_trans' _ _ _ hb (Q'.le_trans' _ _ _ (Q'.le_of_eqv (listQSum_mul_left _ _ _))
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (higher_mass_sum relativeHigher_nonnegative relative_entropy_guard K margin time)
      (by decide : (0 : Q') ≤ 8*qpow (oddRate nome) 14)))

def twoCapPairBudget : Q' :=
  Q'.ofNat spatialCapacity*(8*qpow (oddRate nome) 16)+
    (8*qpow (oddRate nome) 14)*tailBudget spatialCapacity replicaCapacity 1 relativeHigherRate relative_entropy_guard

theorem original_twoCap_pair_sum_bound (K margin time : Nat) :
    listQSum (fun pair => Q'.abs (weightedPairTerm nome K margin pair)) (twoCapPairs K margin time) ≤
      twoCapPairBudget := by
  have he := Q'.eqv_trans _ _ _ (listQSum_perm (fun pair => Q'.abs (weightedPairTerm nome K margin pair))
    (List.filter_append_perm (fun pair => decide (pairHigher margin pair=0)) (twoCapPairs K margin time)).symm)
    (sum_append _ _ _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.add_le_add (fundamental_weight_sum K margin time) (higher_weight_sum K margin time))

theorem twoCapPairBudget_small : twoCapPairBudget ≤ Q'.invSucc (2^15-1)*qpow nome 36 := by decide

theorem original_twoCap_pair_sum_small (K margin time : Nat) :
    listQSum (fun pair => Q'.abs (weightedPairTerm nome K margin pair)) (twoCapPairs K margin time) ≤
      Q'.invSucc (2^15-1)*qpow nome 36 :=
  Q'.le_trans' _ _ _ (original_twoCap_pair_sum_bound K margin time) twoCapPairBudget_small

end YMGap.Continuum.BF4ExactSlabTwoCapPairSum

#print axioms YMGap.Continuum.BF4ExactSlabTwoCapPairSum.fundamentalPairs
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapPairSum.higherPairs
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapPairSum.fundamental_count
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapPairSum.fundamental_weight_sum
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapPairSum.higher_mass_sum
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapPairSum.relative_entropy_guard
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapPairSum.higher_weight_sum
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapPairSum.twoCapPairBudget
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapPairSum.original_twoCap_pair_sum_bound
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapPairSum.twoCapPairBudget_small
#print axioms YMGap.Continuum.BF4ExactSlabTwoCapPairSum.original_twoCap_pair_sum_small
