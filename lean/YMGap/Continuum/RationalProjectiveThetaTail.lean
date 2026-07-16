/-
Exact PF2 tail localization at the rational projective theta head.

For `x=w/(1-w)` and `t=x.num.toNat`, the projective ceiling `x <= t`
implies `1 <= (t+1)(1-w)`.  Reciprocal Bernoulli therefore gives

  `w^(t+1) <= 1/2`.

Four blocks dominate the first omitted exponent at the retained theta head
`b=2t+2`, so its coefficient successor multiplier is at most `1/8`.  The
retune cube is at least `1/8`, and PF2 propagates the comparison to every
later representation.
-/

import YMGap.Continuum.RationalProjectiveThetaHead
import YMGap.Continuum.HarmonicGrowingAnchorPF2

namespace YMGap.Continuum.RationalProjectiveThetaTail

set_option maxHeartbeats 4000000
set_option maxRecDepth 50000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.CutoffCorrelationMonotone
open YMGap.Continuum.BernsteinMonomialReconstruction
open YMGap.Continuum.BernsteinVariance
open YMGap.Continuum.RationalProjectiveThetaHead

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_both {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

/-- Clearing the positive projective denominator turns `w/(1-w) <= t`
into the denominator-free inequality `w <= t(1-w)`. -/
theorem rational_weight_le_index_mul_complement {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hu : (0 : Q') < (1 : Q') - w) :
    w ≤ Q'.ofNat (rationalProjectiveIndex w hu) * ((1 : Q') - w) := by
  let den := rationalProjectiveDen w hu
  let x := rationalProjectiveCoord w hu
  let t := rationalProjectiveIndex w hu
  have hxt : x ≤ Q'.ofNat t := rationalProjectiveCoord_le_index hw0 hu
  have hmul := Q'.mul_le_mul_of_nonneg_right x (Q'.ofNat t)
    ((1 : Q') - w) hxt (Q'.le_of_lt hu)
  have hclear : x * ((1 : Q') - w) ≈ w := by
    dsimp [x, rationalProjectiveCoord, den]
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left w _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
          (rationalProjective_clear_complement w hu))) ?_
    exact Q'.mul_one_eqv w
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hclear) hmul

/-- The successor of the projective ceiling pays one full complementary
unit: `1 <= (t+1)(1-w)`. -/
theorem one_le_succ_index_mul_complement {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hu : (0 : Q') < (1 : Q') - w) :
    (1 : Q') ≤
      Q'.ofNat (rationalProjectiveIndex w hu + 1) * ((1 : Q') - w) := by
  let t := rationalProjectiveIndex w hu
  let u := (1 : Q') - w
  have hwt : w ≤ Q'.ofNat t * u := by
    dsimp [t, u]
    exact rational_weight_le_index_mul_complement hw0 hu
  have hadd : w + u ≤ Q'.ofNat t * u + u :=
    Q'.add_le_add hwt (Q'.le_refl' u)
  have hleft : w + u ≈ (1 : Q') := by
    dsimp [u]
    exact add_one_sub_eqv_one w
  have hright : Q'.ofNat t * u + u ≈ Q'.ofNat (t + 1) * u := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv u))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_mul_eqv _ _ _)) ?_
    exact Q'.mul_eqv_congr_right _ _ u (Q'.eqv_symm (Q'.ofNat_add_eqv t 1))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hright))

/-- The reciprocal-Bernoulli denominator at `t+1` is at least two. -/
theorem two_le_projective_bernDen {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hu : (0 : Q') < (1 : Q') - w) :
    (2 : Q') ≤ bernDen ((1 : Q') - w)
      (rationalProjectiveIndex w hu + 1) := by
  have hone := one_le_succ_index_mul_complement hw0 hu
  have hadd := Q'.add_le_add_left (1 : Q') (1 : Q')
    (Q'.ofNat (rationalProjectiveIndex w hu + 1) * ((1 : Q') - w)) hone
  unfold bernDen
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide)) hadd

/-- One projective block has power at most one half. -/
theorem rational_projective_block_power_le_half {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hu : (0 : Q') < (1 : Q') - w) :
    qpow w (rationalProjectiveIndex w hu + 1) ≤
      Q'.mkPos 1 2 (by decide) := by
  let u := (1 : Q') - w
  let n := rationalProjectiveIndex w hu + 1
  have hu0 : (0 : Q') ≤ u := Q'.le_of_lt hu
  have hu1 : u ≤ (1 : Q') := by
    dsimp [u]
    exact YMGap.Continuum.BondMovingRetuneFix.oneSub_le_one hw0
  have hbern := oneSub_pow_mul_bernDen_le hu0 hu1 n
  have hden : (2 : Q') ≤ bernDen u n := by
    dsimp [u, n]
    exact two_le_projective_bernDen hw0 hu
  have hp0 : (0 : Q') ≤ qpow (oneSub u) n := by
    have hbase0 : (0 : Q') ≤ oneSub u := by
      unfold oneSub
      exact Q'.sub_nonneg_of_le hu1
    exact qpow_nonneg _ hbase0 _
  have h2 : qpow (oneSub u) n * (2 : Q') ≤ (1 : Q') := by
    have hm := Q'.mul_le_mul_of_nonneg_left _ _ (qpow (oneSub u) n) hden hp0
    exact Q'.le_trans' _ _ _ hm hbern
  have hs := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.mkPos 1 2 (by decide)) h2 (by decide)
  have hhalf : qpow (oneSub u) n ≤ Q'.mkPos 1 2 (by decide) := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_)
      (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (Q'.mul_one_eqv _)))
    let p := qpow (oneSub u) n
    change p ≈ Q'.mkPos 1 2 (by decide) * (p * 2)
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv p)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ p
        (by decide : (1 : Q') ≈ Q'.mkPos 1 2 (by decide) * 2)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) ?_
    exact Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv _ _)
  have hbase : oneSub u ≈ w := by
    dsimp [u]
    exact AFRateCalibration.one_sub_one_sub_eqv w
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (BondMovingRelResidual.qpow_eqv_congr_base hbase n)) hhalf

/-- Four projective blocks force the tail power below `1/16`. -/
theorem rational_projective_four_blocks_le_sixteenth {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hu : (0 : Q') < (1 : Q') - w) :
    qpow w (4 * (rationalProjectiveIndex w hu + 1)) ≤
      Q'.mkPos 1 16 (by decide) := by
  let n := rationalProjectiveIndex w hu + 1
  let p := qpow w n
  have hp : p ≤ Q'.mkPos 1 2 (by decide) := by
    dsimp [p, n]
    exact rational_projective_block_power_le_half hw0 hu
  have hp0 : (0 : Q') ≤ p := qpow_nonneg _ hw0 _
  have h2 := Q'.mul_le_mul_of_nonneg hp hp (by decide) hp0
  have h20 : (0 : Q') ≤ p * p := Q'.mul_nonneg _ _ hp0 hp0
  have h4 := Q'.mul_le_mul_of_nonneg h2 h2 (by decide) h20
  have he : qpow w (4 * n) ≈ (p * p) * (p * p) := by
    dsimp [p]
    have hA := qpow_add w n n
    have hB := qpow_add w (2 * n) (2 * n)
    have hidx1 : n + n = 2 * n := by omega
    have hidx2 : 2 * n + 2 * n = 4 * n := by omega
    rw [hidx1] at hA
    rw [hidx2] at hB
    exact Q'.eqv_trans _ _ _ hB (mul_eqv_both hA hA)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.le_trans' _ _ _ h4 (by decide))

/-- At the rational theta head, the generic successor multiplier is at most
`1/8`. -/
theorem rational_head_multiplier_le_eighth {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hu : (0 : Q') < (1 : Q') - w) :
    Q'.ofNat 2 * qpow w (2 * rationalThetaHead w hu + 3) ≤
      Q'.mkPos 1 8 (by decide) := by
  have hw1 : w ≤ (1 : Q') := by
    have := Q'.le_of_lt hu
    exact Q'.le_of_sub_nonneg this
  have hpow : qpow w (2 * rationalThetaHead w hu + 3) ≤
      qpow w (4 * (rationalProjectiveIndex w hu + 1)) := by
    apply qpow_antitone hw0 hw1
    unfold rationalThetaHead
    omega
  have hs := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2) hpow (by decide)
  exact Q'.le_trans' _ _ _ hs
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2)
        (rational_projective_four_blocks_le_sixteenth hw0 hu) (by decide))
      (by decide))

/-- The retune cube is uniformly at least `1/8` on nonnegative couplings. -/
theorem eighth_le_retune_of_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) :
    Q'.mkPos 1 8 (by decide) ≤ retuneCube w := by
  have hb : Q'.mkPos 1 2 (by decide) ≤ retuneBase w := by
    unfold retuneBase
    have h := Q'.add_le_add_left 1 0 w hw0
    have hs := Q'.mul_le_mul_of_nonneg_left _ _
      (Q'.mkPos 1 2 (by decide)) h (by decide)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide)) hs
  exact qpow_mono (by decide) hb 3

/-- The first coefficient beyond the rational theta head is retune-safe. -/
theorem rational_head_tail_step {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hu : (0 : Q') < (1 : Q') - w) :
    coeffW w (rationalThetaHead w hu + 1) ≤
      retuneCube w * coeffW w (rationalThetaHead w hu) := by
  have hw1 : w ≤ (1 : Q') :=
    Q'.le_of_sub_nonneg (Q'.le_of_lt hu)
  have hratio := tailTerm_ratio_gen hw0 hw1 1
    (rationalThetaHead w hu) (rationalThetaHead w hu) (Nat.le_refl _)
  have hmul : Q'.ofNat (2 ^ 1) *
      qpow w (2 * rationalThetaHead w hu + 3) ≤ retuneCube w :=
    Q'.le_trans' _ _ _ (rational_head_multiplier_le_eighth hw0 hu)
      (eighth_le_retune_of_nonneg hw0)
  have hc0 := coeffW_nonneg hw0 (rationalThetaHead w hu)
  have hs := Q'.mul_le_mul_of_nonneg_right _ _ _ hmul hc0
  have hTL : coeffW w (rationalThetaHead w hu + 1) ≈
      tailTerm w 1 (rationalThetaHead w hu + 1) := by
    unfold tailTerm coeffW dimQ
    simp only [Nat.pow_one]
    exact Q'.eqv_refl _
  have hTR : tailTerm w 1 (rationalThetaHead w hu) ≈
      coeffW w (rationalThetaHead w hu) := by
    unfold tailTerm coeffW dimQ
    simp only [Nat.pow_one]
    exact Q'.eqv_refl _
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hTL)
    (Q'.le_trans' _ _ _ hratio ?_)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hTR)) hs

/-- PF2 propagates the rational-head successor comparison to every later
representation. -/
theorem rational_head_all_tail_steps {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwp : (0 : Q') < w)
    (hu : (0 : Q') < (1 : Q') - w) {a : Nat}
    (ha : rationalThetaHead w hu ≤ a) :
    coeffW w (a + 1) ≤ retuneCube w * coeffW w a := by
  by_cases heq : a = rationalThetaHead w hu
  · subst a
    exact rational_head_tail_step hw0 hu
  · have hlt : rationalThetaHead w hu < a :=
      Nat.lt_of_le_of_ne ha (Ne.symm heq)
    have hw1 : w ≤ (1 : Q') :=
      Q'.le_of_sub_nonneg (Q'.le_of_lt hu)
    have hinj := shifted_ratio_injection hw0 hw1 hwp
      (a := rationalThetaHead w hu) (N := a) hlt
    have hca0 := coeffW_nonneg hw0 a
    have hmul := Q'.mul_le_mul_of_nonneg_right _ _ _
      (rational_head_tail_step hw0 hu) hca0
    have hchain : coeffW w (rationalThetaHead w hu) * coeffW w (a + 1) ≤
        coeffW w (rationalThetaHead w hu) *
          (retuneCube w * coeffW w a) := by
      refine Q'.le_trans' _ _ _ hinj ?_
      refine Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv ?_)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
      exact Q'.mul_assoc_eqv _ _ _
    exact Q'.le_of_mul_le_mul_left hchain
      (FusionResidualBound.coeffW_pos hwp (rationalThetaHead w hu))

end YMGap.Continuum.RationalProjectiveThetaTail

#print axioms YMGap.Continuum.RationalProjectiveThetaTail.rational_weight_le_index_mul_complement
#print axioms YMGap.Continuum.RationalProjectiveThetaTail.rational_projective_block_power_le_half
#print axioms YMGap.Continuum.RationalProjectiveThetaTail.rational_head_multiplier_le_eighth
#print axioms YMGap.Continuum.RationalProjectiveThetaTail.rational_head_tail_step
#print axioms YMGap.Continuum.RationalProjectiveThetaTail.rational_head_all_tail_steps
