/-
# A rounded-cutoff upper bound for the original SU(2) heat series

At the actual nome `0 < w < 1`, let `N = HeatRoundedCutoff.cutoff w`.
The squared-dimension heat majorant is at most `4^n` at every label and
at most `(1/2)^n` for `n >= N`. Hence every original majorant prefix is
at most `4^N + 2`, and the existing finite-head/closed-tail `prefixCap`
is at most `4^(N+1)`. No lower heat window, interacting contraction,
physical spectral identification, or continuum conclusion is assumed.
-/

import YMGap.Continuum.HeatRoundedCutoff
import YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
import YMGap.Continuum.FiveHolonomyPerronCutoff

namespace YMGap.Continuum.SU2RoundedHeatUpper

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion
open YMGap.Continuum.SU2PointwiseHeatSpacingTailBound
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem succ_le_two_pow : ∀ n : Nat, n + 1 ≤ 2 ^ n
  | 0 => by decide
  | n + 1 => by
      have h := Nat.mul_le_mul_left 2 (succ_le_two_pow n)
      have hs : n + 2 ≤ 2 * (n + 1) := by omega
      simpa only [Nat.pow_succ, Nat.mul_comm] using Nat.le_trans hs h

private theorem dimension_square_le_four_pow (n : Nat) :
    (n + 1) ^ 2 ≤ 4 ^ n := by
  have h := Nat.pow_le_pow_left (succ_le_two_pow n) 2
  have he : (2 ^ n) ^ 2 = (2 ^ 2) ^ n := by
    rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm n 2]
  simpa only [he] using h

private theorem ofNat_four_pow : ∀ n : Nat,
    Q'.ofNat (4 ^ n) ≈ (4 : Q') ^ n
  | 0 => Q'.eqv_refl 1
  | n + 1 => by
      rw [Nat.pow_succ]
      exact Q'.eqv_trans _ _ _ (HeatKernelRGStep.ofNat_mul_eqv (4 ^ n) 4)
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ (4 : Q') (ofNat_four_pow n))
          (Q'.mul_comm_eqv _ _))

private theorem dimension_square_bound (n : Nat) :
    Q'.ofNat ((n + 1) ^ 2) ≤ (4 : Q') ^ n :=
  Q'.le_trans' _ _ _ (CReal.ofNat_le_ofNat (dimension_square_le_four_pow n))
    (Q'.le_of_eqv (ofNat_four_pow n))

private theorem one_le_four_pow : ∀ n : Nat, (1 : Q') ≤ (4 : Q') ^ n
  | 0 => Q'.le_refl' 1
  | n + 1 =>
      Q'.le_trans' _ _ _ (by decide : (1 : Q') ≤ 4)
        (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv 4))
          (Q'.mul_le_mul_of_nonneg_left _ _ 4 (one_le_four_pow n) (by decide)))

private theorem four_pow_mono {m n : Nat} (hmn : m ≤ n) :
    (4 : Q') ^ m ≤ (4 : Q') ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (one_le_four_pow k)
        (Q'.pow_nonneg 4 (by decide) m))
      (Q'.ge_of_eqv (Q'.pow_add_eqv 4 m k)))

private theorem four_pow_mul_eighth_pow : ∀ n : Nat,
    (4 : Q') ^ n * eighth ^ n ≈ half ^ n
  | 0 => Q'.mul_one_eqv 1
  | n + 1 => by
      have he :
          ((4 : Q') * (4 : Q') ^ n) * (eighth * eighth ^ n) ≈
            half * ((4 : Q') ^ n * eighth ^ n) := by
        have hreorder := poly_identity_of_normal_eq
          (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
          (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide)
          (fun | 0 => (4 : Q') | 1 => (4 : Q') ^ n | 2 => eighth | _ => eighth ^ n)
        exact Q'.eqv_trans _ _ _ hreorder
          (Q'.mul_eqv_congr_right _ _ _ (by decide : (4 : Q') * eighth ≈ half))
      exact Q'.eqv_trans _ _ _ he
        (Q'.mul_eqv_congr_left half _ _ (four_pow_mul_eighth_pow n))

/-- The unsuppressed dimension bound, valid at every original label. -/
theorem majorant_le_four_pow {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (n : Nat) :
    pointwiseHeatMajorant w n ≤ (4 : Q') ^ n := by
  have hp := HeatKernelGap.qpow_le_one (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) (c4 n)
  change Q'.ofNat ((n + 1) ^ 2) * qpow w (c4 n) ≤ _
  exact Q'.le_trans' _ _ _
    (HKConv.mul_le_mul' (HeatKernelRGStep.zero_le_ofNat _) Q'.zero_le_one
      (dimension_square_bound n) hp)
    (Q'.le_of_eqv (Q'.mul_one_eqv _))

/-- Beyond the actual rounded cutoff, the original Casimir beats the
squared dimension, with the explicit half-geometric majorant. -/
theorem majorant_le_half_pow_of_cutoff_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (n : Nat) (hn : HeatRoundedCutoff.cutoff w ≤ n) :
    pointwiseHeatMajorant w n ≤ half ^ n := by
  let N := HeatRoundedCutoff.cutoff w
  have hexp : N * n ≤ c4 n := by
    have h := Nat.mul_le_mul_right n (show N ≤ n + 2 by dsimp [N]; omega)
    simpa only [c4, Nat.mul_comm] using h
  have hp : qpow w (c4 n) ≤ eighth ^ n :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (qpow_eqv_pow w (c4 n)))
      (Q'.le_trans' _ _ _
        (HKConvGen.pow_base_antitone (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hexp)
        (Q'.le_trans' _ _ _
          (Q'.ge_of_eqv (FiveHolonomyPerronCutoff.pow_mul_eqv w N n))
          (HKConv.pow_le_pow_base (Q'.pow_nonneg w (Q'.le_of_lt hw0) N)
            (HeatRoundedCutoff.power_le hw0 hw1) n)))
  change Q'.ofNat ((n + 1) ^ 2) * qpow w (c4 n) ≤ _
  exact Q'.le_trans' _ _ _
    (HKConv.mul_le_mul' (HeatKernelRGStep.zero_le_ofNat _)
      (Q'.pow_nonneg eighth (by decide) n) (dimension_square_bound n) hp)
    (Q'.le_of_eqv (four_pow_mul_eighth_pow n))

private theorem geometric_head_bound : ∀ K : Nat,
    finSum (fun n => (4 : Q') ^ n) K ≤ (4 : Q') ^ K
  | 0 => by decide
  | K + 1 => by
      have he : (4 : Q') ^ K + (4 : Q') ^ K ≈ (2 : Q') * (4 : Q') ^ K :=
        poly_identity_of_normal_eq (.add (.var 0) (.var 0))
          (.mul (.const 2) (.var 0)) (by decide) (fun _ => (4 : Q') ^ K)
      exact Q'.le_trans' _ _ _
        (Q'.add_le_add_right _ _ _ (geometric_head_bound K))
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
          (Q'.mul_le_mul_of_nonneg_right _ _ _ (by decide : (2 : Q') ≤ 4)
            (Q'.pow_nonneg 4 (by decide) K)))

private theorem majorant_head_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) :
    finSum (pointwiseHeatMajorant w) K ≤ (4 : Q') ^ K :=
  Q'.le_trans' _ _ _
    (CharacterTail.finSum_le_termwise _ _ (majorant_le_four_pow hw0 hw1) K)
    (geometric_head_bound K)

private theorem half_geometric_bound (K : Nat) :
    finSum (fun n => half ^ n) K ≤ (2 : Q') :=
  CharacterTail.geom_series_le (fun n => half ^ n) 1 half 2 (by decide) (by decide)
    (Q'.le_refl' 1) (fun _ => Q'.le_refl' _) (by decide) K

/-- Every original majorant prefix has a bound independent of its
truncation, with rounded-nome dependence explicit. -/
theorem majorant_prefix_le_rounded {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) :
    finSum (pointwiseHeatMajorant w) K ≤
      (4 : Q') ^ HeatRoundedCutoff.cutoff w + 2 := by
  let N := HeatRoundedCutoff.cutoff w
  by_cases hK : K ≤ N
  · exact Q'.le_trans' _ _ _ (majorant_head_bound hw0 hw1 K)
      (Q'.le_trans' _ _ _ (four_pow_mono hK)
        (Q'.add_le_self_of_nonneg _ 2 (by decide)))
  · have hNK : N ≤ K := by omega
    have hsplit := FiveHolonomyPerronCutoff.finSum_split (pointwiseHeatMajorant w) N (K-N)
    rw [Nat.add_sub_of_le hNK] at hsplit
    have htail : finSum (fun i => pointwiseHeatMajorant w (N+i)) (K-N) ≤ (2 : Q') :=
      Q'.le_trans' _ _ _
        (CharacterTail.finSum_le_termwise _ _ (fun i =>
          Q'.le_trans' _ _ _
            (majorant_le_half_pow_of_cutoff_le hw0 hw1 (N+i) (by dsimp [N]; omega))
            (HKConvGen.pow_base_antitone (by decide : (0 : Q') ≤ half)
              (by decide : half ≤ (1 : Q')) (Nat.le_add_left i N))) (K-N))
        (half_geometric_bound (K-N))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit)
      (Q'.add_le_add (majorant_head_bound hw0 hw1 N) htail)

/-- A uniform individual-label bound for the same original majorant. -/
theorem majorant_le_rounded_pow {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (n : Nat) :
    pointwiseHeatMajorant w n ≤ (4 : Q') ^ HeatRoundedCutoff.cutoff w := by
  by_cases hn : n ≤ HeatRoundedCutoff.cutoff w
  · exact Q'.le_trans' _ _ _ (majorant_le_four_pow hw0 hw1 n) (four_pow_mono hn)
  · exact Q'.le_trans' _ _ _
      (majorant_le_half_pow_of_cutoff_le hw0 hw1 n (by omega))
      (Q'.le_trans' _ _ _ (HKPos.pow_le_one (by decide) (by decide) n)
        (one_le_four_pow _))

private theorem raw_tail_reciprocal_le_two {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    HKConv.divPos 1 (1 + -spacingTailRatio w) ≤ (2 : Q') := by
  have hgap : half ≤ 1 + -spacingTailRatio w :=
    Q'.le_trans' _ _ _ (by decide : half ≤ (1 : Q') + -half)
      (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg (spacingTailRatio_le_half hw0 hw1)))
  apply HKConv.divPos_le_of_le
    (CReal.num_pos_of_pos (HKPos.one_sub_pos (spacingTailRatio_lt_one hw0 hw1)))
  exact Q'.le_trans' _ _ _ (by decide : (1 : Q') ≤ (2 : Q') * half)
    (Q'.mul_le_mul_of_nonneg_left _ _ 2 hgap (by decide))

/-- The old raw-cutoff closed tail is paid for without estimating the
representation-dependent size of that cutoff. -/
theorem closedTail_zero_le_rounded {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    spacingClosedTail w 0 ≤ (2 : Q') * (4 : Q') ^ HeatRoundedCutoff.cutoff w := by
  rw [spacingClosedTail_formula]
  have he : (spacingTailHead w * spacingTailRatio w ^ 0) *
      HKConv.divPos 1 (1 + -spacingTailRatio w) ≈
      spacingTailHead w * HKConv.divPos 1 (1 + -spacingTailRatio w) :=
    Q'.mul_eqv_congr_right _ _ _ (Q'.mul_one_eqv _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.le_trans' _ _ _
      (HKConv.mul_le_mul' (spacingTailHead_nonnegative hw0) (by decide : (0 : Q') ≤ 2)
        (majorant_le_rounded_pow hw0 hw1 (spacingLabelCutoff w))
        (raw_tail_reciprocal_le_two hw0 hw1))
      (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))

/-- The existing full-prefix cap has an explicit rounded bit cost `N+1`,
at every genuine nome, without a small-nome or physical spectral input. -/
theorem prefixCap_le_rounded_pow {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    prefixCap w ≤ (4 : Q') ^ (HeatRoundedCutoff.cutoff w + 1) := by
  let A := (4 : Q') ^ HeatRoundedCutoff.cutoff w
  have hfour : (4 : Q') ≤ A :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv 4))
      (four_pow_mono (HeatRoundedCutoff.cutoff_positive w))
  have htwo : (2 : Q') ≤ A := Q'.le_trans' _ _ _ (by decide) hfour
  have he : (A + A) + (2 : Q') * A ≈ (4 : Q') * A :=
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 0)) (.mul (.const 2) (.var 0)))
      (.mul (.const 4) (.var 0)) (by decide) (fun _ => A)
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add (majorant_prefix_le_rounded hw0 hw1 (spacingLabelCutoff w))
      (closedTail_zero_le_rounded hw0 hw1))
    (Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ ((2 : Q') * A) (Q'.add_le_add_left A 2 A htwo))
      (Q'.le_of_eqv he))

#print axioms majorant_le_four_pow
#print axioms majorant_le_half_pow_of_cutoff_le
#print axioms majorant_prefix_le_rounded
#print axioms majorant_le_rounded_pow
#print axioms closedTail_zero_le_rounded
#print axioms prefixCap_le_rounded_pow

end YMGap.Continuum.SU2RoundedHeatUpper
