/-
# Sum the ORIGINAL zero-spatial short-pair weights uniformly

The proved H-stratum count combines with the original sharp heat envelope.
The entire zeroSpatialPairs list has summed absolute weight at most the
explicit geometric budget 8*oddRate^12*(M*r)/(1-M*r), M=2*shortFaceCapacity.
At the unchanged nome this is <=2^-20*w^36, uniformly in cutoff, margin
and cut-filter time. This is an aggregate bound, not just per-pair smallness.

The individual detached partition squares are NOT included in this sum.
Their uniform short-collar comparison and the spatial-defect remainder
remain necessary before bounding shortOtherRemainder or the full response.
-/

import YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount
import YMGap.Continuum.BF4ExactSlabZeroSpatialHeatBound
import YMGap.Continuum.FiniteSizeGeometricSum

namespace YMGap.Continuum.BF4ExactSlabZeroSpatialPairSum

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2ParityHigherHeatEnvelope
open YMGap.Continuum.BF4ExactSlabLocalizedHigherCode
open YMGap.Continuum.BF4ExactSlabShortCoreLocalization
open YMGap.Continuum.BF4ExactSlabZeroSpatialPairCount
open YMGap.Continuum.BF4ExactSlabZeroSpatialHeatBound
open YMGap.Continuum.BF4ExactSlabParityHigherPairBound
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate (nome)
open YMGap.Continuum.PairedPositiveFaceLabellings

local infix:50 " ≈ " => Q'.eqv

theorem codeHigher_bound (K : Nat) : ∀ code : List (Nat × Nat),
    (∀ entry, entry ∈ code → entry.1+entry.2 ≤ K) → codeHigher code ≤ code.length*K
  | [], _ => Nat.zero_le _
  | entry::rest, h => by
    have hh := h entry List.mem_cons_self
    have ih := codeHigher_bound K rest (fun e he => h e (List.mem_cons_of_mem entry he))
    change entry.1+entry.2+codeHigher rest ≤ (rest.length+1)*K
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem original_higher_upper {K margin time : Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hp : pair ∈ zeroSpatialPairs K margin time) : pairHigher margin pair ≤ shortFaceCapacity*K := by
  obtain ⟨_,ids,hs,hm⟩ := zeroSpatialPairs_mem hp
  have hc := codeHigher_bound K (higherCode margin pair) (by
    intro entry he
    have hb := higherCode_bounded hm entry he
    omega)
  rw [higherCode_power hs hm] at hc
  exact Nat.le_trans hc (Nat.mul_le_mul_right K (higherCode_length_le margin pair))

theorem original_higher_sum_bound {r : Q'} (hr : (0 : Q') ≤ r)
    (hs : entropyRate replicaCapacity r < 1) (K margin time : Nat) (hK : 1 ≤ K) :
    listQSum (fun pair => r^(pairHigher margin pair)) (zeroSpatialPairs K margin time) ≤
      tailBudget 1 replicaCapacity 1 r hs := by
  apply size_sum_bound _ (pairHigher margin) 1 replicaCapacity 1 (shortFaceCapacity*K) hr hs
    (fun _ hp => zeroSpatialPairs_higher_positive hK hp) (fun _ hp => original_higher_upper hp)
  intro H
  have he : (zeroSpatialPairs K margin time).filter (fun pair => decide (H = pairHigher margin pair)) =
      (zeroSpatialPairs K margin time).filter (fun pair => decide (pairHigher margin pair = H)) := by
    apply List.filter_congr
    intro pair _
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact eq_comm
  rw [he, Nat.one_mul]
  exact original_mass_stratum_count K margin time H

private theorem qpow_to_pow (w : Q') : ∀ n : Nat, qpow w n ≈ w^n
  | 0 => Q'.eqv_refl 1
  | n+1 => Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ w (qpow_to_pow w n)) (Q'.mul_comm_eqv _ _)

def zeroSpatialPairBudget (w : Q') (hs : entropyRate replicaCapacity (higherRate w) < 1) : Q' :=
  (8*qpow (oddRate w) 12)*tailBudget 1 replicaCapacity 1 (higherRate w) hs

/-- Sum of absolute ORIGINAL weights, including original representation multiplicities. -/
theorem original_weight_abs_sum_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1)
    (hs : entropyRate replicaCapacity (higherRate w) < 1) (K margin time : Nat) (hK : 1 ≤ K) :
    listQSum (fun pair => Q'.abs (weightedPairTerm w K margin pair)) (zeroSpatialPairs K margin time) ≤
      zeroSpatialPairBudget w hs := by
  have hp := sum_le_on (fun pair => Q'.abs (weightedPairTerm w K margin pair))
    (fun pair => (8*qpow (oddRate w) 12)*(higherRate w)^(pairHigher margin pair))
    (zeroSpatialPairs K margin time) (by
      intro pair hm
      obtain ⟨hc,ids,hids,hpair⟩ := zeroSpatialPairs_mem hm
      have hb := weightedPairTerm_parity_bound hw0 hw1 K margin pair
        (fun id _ => bounded K ids pair hpair id)
      rw [nonzero_pairParity_twelve margin pair hc.1 hc.2.1 hc.2.2] at hb
      exact Q'.le_trans' _ _ _ hb (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 8 _ _
          (Q'.mul_eqv_congr_left (qpow (oddRate w) 12) _ _ (qpow_to_pow _ _)))
          (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))))
  exact Q'.le_trans' _ _ _ hp
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (listQSum_mul_left _ _ _))
      (Q'.mul_le_mul_of_nonneg_left _ _ (8*qpow (oddRate w) 12)
        (original_higher_sum_bound (higherRate_nonnegative hw0) hs K margin time hK)
        (Q'.mul_nonneg _ _ (by decide) (qpow_nonneg _ (oddRate_nonnegative hw0) 12))))

theorem existingNome_local_rate_guard : entropyRate replicaCapacity (higherRate nome) < 1 := by decide

theorem existingNome_budget_small : zeroSpatialPairBudget nome existingNome_local_rate_guard ≤
    Q'.invSucc (2^20-1)*qpow nome 36 := by decide

/-- Uniform in cutoff, volume margin and cut-filter time; detached partitions are still separate. -/
theorem existingNome_original_weight_abs_sum_bound (K margin time : Nat) (hK : 1 ≤ K) :
    listQSum (fun pair => Q'.abs (weightedPairTerm nome K margin pair)) (zeroSpatialPairs K margin time) ≤
      Q'.invSucc (2^20-1)*qpow nome 36 :=
  Q'.le_trans' _ _ _ (original_weight_abs_sum_bound (by decide) (by decide)
    existingNome_local_rate_guard K margin time hK) existingNome_budget_small

end YMGap.Continuum.BF4ExactSlabZeroSpatialPairSum

#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialPairSum.codeHigher_bound
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialPairSum.original_higher_upper
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialPairSum.original_higher_sum_bound
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialPairSum.zeroSpatialPairBudget
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialPairSum.original_weight_abs_sum_bound
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialPairSum.existingNome_local_rate_guard
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialPairSum.existingNome_budget_small
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialPairSum.existingNome_original_weight_abs_sum_bound
