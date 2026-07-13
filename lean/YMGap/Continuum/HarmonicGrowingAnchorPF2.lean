/-
# Growing-anchor PF2 localization on the harmonic trajectory

The fixed three-coordinate localization fails at `k=18`.  Here the retained
depth grows linearly, `S_k=2(k+2)`.  Reciprocal Bernoulli gives
`harmW(k)^(k+2) <= 1/2`; four such blocks force the first omitted coefficient
ratio below `1/8`, uniformly in `k`.  Since the retune cube is at least
`(3/4)^3=27/64`, PF2 makes every later ratio safe as well.
-/

import YMGap.Continuum.HarmonicThetaRatioExtension
import YMGap.Continuum.HarmonicBulkThetaTail
import YMGap.Continuum.HarmonicFusedSchurObstruction

namespace YMGap.Continuum.HarmonicGrowingAnchorPF2

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicBulkThetaTail
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.CutoffCorrelationMonotone
open YMGap.Continuum.QuadraticCutoffSchedule

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl
local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one]; ac_rfl))

/-- Linear retained depth used by the growing-anchor localization. -/
def growingAnchor (k : Nat) : Nat := 2 * (k + 2)

/-- The growing anchor remains inside the physical quadratic character cutoff. -/
theorem growingAnchor_le_Ncut (k : Nat) : growingAnchor k ≤ Ncut k := by
  unfold growingAnchor Ncut
  have h := Nat.mul_le_mul_right (k + 2) (show 2 ≤ k + 2 by omega)
  simpa [Nat.mul_comm] using h

private theorem mul_eqv_both {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

/-- Reciprocal Bernoulli at one harmonic block: `w_k^(k+2) <= 1/2`. -/
theorem harmonic_block_power_le_half (k : Nat) :
    qpow (harmW k) (k + 2) ≤ Q'.mkPos 1 2 (by decide) := by
  have h := oneSub_pow_mul_bernDen_le (harmU_nonneg k) (harmU_le_one k) (k + 2)
  have hden : bernDen (harmU k) (k + 2) ≈ (2 : Q') := by
    unfold bernDen harmU unit
    have hm : Q'.ofNat (k + 2) * Q'.mkPos 1 (k + 2) (by omega) ≈ (1 : Q') := by
      show _ * (_ : Int) = _ * (_ : Int)
      simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
        Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den]
      have h1n : (1 : Q').num = 1 := rfl
      have h1d : ((1 : Q').den : Int) = 1 := rfl
      rw [h1n, h1d]
      push_cast
      omega
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left 1 _ _ hm) ?_
    decide
  have h2 : qpow (harmW k) (k + 2) * (2 : Q') ≤ (1 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hden))) h
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.mkPos 1 2 (by decide)) h2 (by decide)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_)
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (Q'.mul_one_eqv _)))
  let p := qpow (harmW k) (k + 2)
  change p ≈ Q'.mkPos 1 2 (by decide) * (p * 2)
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv p)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ p
      (by decide : (1 : Q') ≈ Q'.mkPos 1 2 (by decide) * 2)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) ?_
  exact Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _)

/-- Four harmonic blocks make the power at exponent `4(k+2)` at most `1/16`. -/
theorem harmonic_four_blocks_le_sixteenth (k : Nat) :
    qpow (harmW k) (4 * (k + 2)) ≤ Q'.mkPos 1 16 (by decide) := by
  let p := qpow (harmW k) (k + 2)
  have hp := harmonic_block_power_le_half k
  have hp0 : (0 : Q') ≤ p := qpow_nonneg _ (harmW_nonneg k) _
  have h2 := Q'.mul_le_mul_of_nonneg hp hp (by decide) hp0
  have h20 : (0 : Q') ≤ p * p := Q'.mul_nonneg _ _ hp0 hp0
  have h4 := Q'.mul_le_mul_of_nonneg h2 h2 (by decide) h20
  have he : qpow (harmW k) (4 * (k + 2)) ≈ (p * p) * (p * p) := by
    unfold p
    have hA := qpow_add (harmW k) (k + 2) (k + 2)
    have hB := qpow_add (harmW k) (2 * (k + 2)) (2 * (k + 2))
    have hidx1 : (k + 2) + (k + 2) = 2 * (k + 2) := by omega
    have hidx2 : 2 * (k + 2) + 2 * (k + 2) = 4 * (k + 2) := by omega
    rw [hidx1] at hA
    rw [hidx2] at hB
    exact Q'.eqv_trans _ _ _ hB (mul_eqv_both hA hA)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.le_trans' _ _ _ h4 (by decide))

/-- The generic coefficient-tail multiplier at the growing anchor is at most `1/8`. -/
theorem growing_anchor_multiplier_le_eighth (k : Nat) :
    Q'.ofNat 2 * qpow (harmW k) (2 * growingAnchor k + 3) ≤
      Q'.mkPos 1 8 (by decide) := by
  have hw0 := harmW_nonneg k
  have hw1 := harmW_le_one k
  have hpow : qpow (harmW k) (2 * growingAnchor k + 3) ≤
      qpow (harmW k) (4 * (k + 2)) := by
    apply qpow_antitone hw0 hw1
    unfold growingAnchor
    omega
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2) hpow (by decide)
  exact Q'.le_trans' _ _ _ hs
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2)
        (harmonic_four_blocks_le_sixteenth k) (by decide)) (by decide))

/-- Uniform lower bound on the retune cube along the harmonic trajectory. -/
theorem eighth_le_harmonic_retune (k : Nat) :
    Q'.mkPos 1 8 (by decide) ≤ retuneCube (harmW k) := by
  have hb : Q'.mkPos 1 2 (by decide) ≤ retuneBase (harmW k) := by
    unfold retuneBase
    have h := Q'.add_le_add_left 1 0 (harmW k) (harmW_nonneg k)
    have hs := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.mkPos 1 2 (by decide)) h (by decide)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide)) hs
  exact qpow_mono (by decide) hb 3

/-- **Uniform growing-anchor tail step.**  At depth `2(k+2)`, the first
omitted coefficient ratio is below the retune factor. -/
theorem growing_anchor_tail_step (k : Nat) :
    coeffW (harmW k) (growingAnchor k + 1) ≤
      retuneCube (harmW k) * coeffW (harmW k) (growingAnchor k) := by
  have hratio := tailTerm_ratio_gen (harmW_nonneg k) (harmW_le_one k)
    1 (growingAnchor k) (growingAnchor k) (Nat.le_refl _)
  have hmul : Q'.ofNat (2 ^ 1) * qpow (harmW k) (2 * growingAnchor k + 3) ≤
      retuneCube (harmW k) :=
    Q'.le_trans' _ _ _ (growing_anchor_multiplier_le_eighth k)
      (eighth_le_harmonic_retune k)
  have hc0 := coeffW_nonneg (harmW_nonneg k) (growingAnchor k)
  have hs := Q'.mul_le_mul_of_nonneg_right _ _ _ hmul hc0
  have hTL : coeffW (harmW k) (growingAnchor k + 1) ≈
      tailTerm (harmW k) 1 (growingAnchor k + 1) := by
    unfold tailTerm coeffW dimQ
    simp only [Nat.pow_one]
    exact Q'.eqv_refl _
  have hTR : tailTerm (harmW k) 1 (growingAnchor k) ≈
      coeffW (harmW k) (growingAnchor k) := by
    unfold tailTerm coeffW dimQ
    simp only [Nat.pow_one]
    exact Q'.eqv_refl _
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hTL)
    (Q'.le_trans' _ _ _ hratio ?_)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hTR)) hs

/-- PF2 propagates the growing-anchor step to every later representation. -/
theorem growing_anchor_all_tail_steps (k : Nat) {a : Nat}
    (ha : growingAnchor k ≤ a) :
    coeffW (harmW k) (a + 1) ≤
      retuneCube (harmW k) * coeffW (harmW k) a := by
  by_cases heq : a = growingAnchor k
  · subst a
    exact growing_anchor_tail_step k
  · have hlt : growingAnchor k < a := Nat.lt_of_le_of_ne ha (Ne.symm heq)
    have hinj := shifted_ratio_injection (harmW_nonneg k) (harmW_le_one k)
      (HarmonicFusedSchurObstruction.harmW_pos k)
      (a := growingAnchor k) (N := a) hlt
    have hca0 := coeffW_nonneg (harmW_nonneg k) a
    have hmul := Q'.mul_le_mul_of_nonneg_right _ _ _ (growing_anchor_tail_step k) hca0
    have hchain : coeffW (harmW k) (growingAnchor k) * coeffW (harmW k) (a + 1) ≤
        coeffW (harmW k) (growingAnchor k) *
          (retuneCube (harmW k) * coeffW (harmW k) a) := by
      refine Q'.le_trans' _ _ _ hinj ?_
      refine Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv ?_)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
      exact Q'.mul_assoc_eqv _ _ _
    exact Q'.le_of_mul_le_mul_left hchain
      (FusionResidualBound.coeffW_pos
        (HarmonicFusedSchurObstruction.harmW_pos k) (growingAnchor k))

end YMGap.Continuum.HarmonicGrowingAnchorPF2

#print axioms YMGap.Continuum.HarmonicGrowingAnchorPF2.harmonic_block_power_le_half
#print axioms YMGap.Continuum.HarmonicGrowingAnchorPF2.growingAnchor_le_Ncut
#print axioms YMGap.Continuum.HarmonicGrowingAnchorPF2.harmonic_four_blocks_le_sixteenth
#print axioms YMGap.Continuum.HarmonicGrowingAnchorPF2.growing_anchor_multiplier_le_eighth
#print axioms YMGap.Continuum.HarmonicGrowingAnchorPF2.eighth_le_harmonic_retune
#print axioms YMGap.Continuum.HarmonicGrowingAnchorPF2.growing_anchor_tail_step
#print axioms YMGap.Continuum.HarmonicGrowingAnchorPF2.growing_anchor_all_tail_steps
