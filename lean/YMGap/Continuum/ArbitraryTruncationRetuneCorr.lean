/-
# Arbitrary-truncation retune bound from a correlation/Rayleigh mechanism

For `c_a = coeffW w a = (a+1) w^{a(a+2)}`, define

    A_N = Σ_{a<N} c_a c_{a+1},     D_N = Σ_{a≤N} c_a².

The Peter–Weyl-normalized fundamental fused eigenvalue is `A_N / D_N`.
This module proves, for every truncation `N` and the whole strong window
`0 ≤ w ≤ 1/2`, the cross-multiplied retune inequality

    A_N ≤ ((1+w)/2)^3 D_N.

The proof is independent of the finite `N=3` Bernstein certificate:

1. PF₂/log-concavity gives `c_{a+1} c_0 ≤ c_a c_1`; multiplying by
   `c_a ≥ 0` and using `c_0=1` gives
   `c_a c_{a+1} ≤ c_1 c_a²`.
2. Summing at arbitrary cutoff yields `A_N ≤ c_1 Σ_{a<N}c_a² ≤ c_1 D_N`.
3. On `w≤1/2`, `c_1=2w³≤w/2`.  For `r=(1+w)/2`, the square identity
   `r²-w=(1-w)²/4≥0`, together with `r≥1/2`, gives `w/2≤r³`.

No frontier type is modified or inhabited.  The residual outside the strong
window `1/2 < w ≤ 1` is left explicit; no assumed field is introduced.
-/

import YMGap.Continuum.CubeRatioBounds
import YMGap.Continuum.MultiLinkFusionDefect
import YMGap.Continuum.BondMovingRelResidual
import YMGap.Continuum.BondMovingRetuneFix

namespace YMGap.Continuum.ArbitraryTruncationRetuneCorr

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.MultiLinkFusionDefect
open YMGap.Continuum.BondMovingRelResidual
open YMGap.Continuum.BondMovingRetuneFix
open YMGap.Continuum.CubeRatioBounds

private def half : Q' := Q'.mkPos 1 2 (by decide)
private def quarter : Q' := Q'.mkPos 1 4 (by decide)

/-- Adjacent-coordinate correlation `A_N`. -/
def adjCorr (w : Q') (N : Nat) : Q' :=
  fsum (fun a => coeffW w a * coeffW w (a + 1)) N

/-- Squared norm `D_N`, including the terminal coordinate `a=N`. -/
def coordNormSq (w : Q') (N : Nat) : Q' :=
  fsum (fun a => coeffW w a * coeffW w a) (N + 1)

/-- Corrected `p=2` retune base `(1+w)/2`. -/
def retuneBase (w : Q') : Q' := half * ((1 : Q') + w)

/-- Fundamental retuned heat-kernel eigenvalue `((1+w)/2)^3`. -/
def retuneCube (w : Q') : Q' := qpow (retuneBase w) 3

theorem adjCorr_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (N : Nat) :
    (0 : Q') ≤ adjCorr w N :=
  fsum_nonneg (fun a => Q'.mul_nonneg _ _
    (coeffW_nonneg hw0 a) (coeffW_nonneg hw0 (a + 1))) N

theorem coordNormSq_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (N : Nat) :
    (0 : Q') ≤ coordNormSq w N :=
  fsum_nonneg (fun a => Q'.mul_nonneg _ _
    (coeffW_nonneg hw0 a) (coeffW_nonneg hw0 a)) (N + 1)

/-- `qpow 0 n = 0` for positive `n`. -/
theorem qpow_zero_of_pos : ∀ n : Nat, 0 < n → (qpow (0 : Q') n).eqv 0
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | _ + 1, _ => Q'.mul_zero_eqv _

/-- At a base equivalent to zero every excited coefficient vanishes. -/
theorem coeffW_excited_zero {w : Q'} (hw : w.eqv 0) (a : Nat) :
    (coeffW w (a + 1)).eqv 0 := by
  unfold coeffW
  have hp : (qpow w (c4 (a + 1))).eqv (qpow (0 : Q') (c4 (a + 1))) :=
    qpow_eqv_congr_base hw (c4 (a + 1))
  have hcpos : 0 < c4 (a + 1) := by
    unfold c4
    exact Nat.mul_pos (Nat.succ_pos a) (by omega)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (dimQ (a + 1)) _ _ hp) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (dimQ (a + 1)) _ _ (qpow_zero_of_pos _ hcpos)) ?_
  exact Q'.mul_zero_eqv _

/-- Nonnegative and not equivalent to zero implies strictly positive for `Q'`. -/
theorem pos_of_nonneg_not_eqv_zero {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hwne : ¬ w.eqv 0) : (0 : Q') < w := by
  have hn : (0 : Int) ≤ w.num := (Q'.zero_le_iff_num_nonneg w).mp hw0
  have hne : w.num ≠ 0 := by
    intro hnum
    apply hwne
    show w.num * (1 : Int) = (0 : Int) * (w.den : Int)
    simp [hnum]
  show (0 : Int) * (w.den : Int) < w.num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  omega

/-- PF₂ termwise correlation bound:
`c_a c_{a+1} ≤ c_1 c_a²`. -/
theorem adjacent_term_le_anchor {w : Q'} (hwp : (0 : Q') < w)
    (hw1 : w ≤ (1 : Q')) (a : Nat) :
    coeffW w a * coeffW w (a + 1)
      ≤ coeffW w 1 * (coeffW w a * coeffW w a) := by
  have hr := ratio_to_sq (coeffW_nonneg (Q'.le_of_lt hwp) a)
    (coeffW_ratio_le hwp hw1 a)
  rw [coeffW_zero] at hr
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.one_mul_eqv _))) hr

/-- Arbitrary-cutoff correlation bound `A_N ≤ c₁ D_N`. -/
theorem adjCorr_le_anchor_norm {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (N : Nat) :
    adjCorr w N ≤ coeffW w 1 * coordNormSq w N := by
  by_cases hwz : w.eqv 0
  · have hzero : (adjCorr w N).eqv 0 := by
      unfold adjCorr
      refine Q'.eqv_trans _ _ _
        (fsum_eqv_congr _ (fun _ => (0 : Q')) (fun a => ?_) N) ?_
      · refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (coeffW w a) _ _ (coeffW_excited_zero hwz a)) ?_
        exact Q'.mul_zero_eqv _
      · rw [fsum_zero_seq]
        exact Q'.eqv_refl 0
    have hR : (0 : Q') ≤ coeffW w 1 * coordNormSq w N :=
      Q'.mul_nonneg _ _ (coeffW_nonneg hw0 1) (coordNormSq_nonneg hw0 N)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hzero) hR
  · have hwp : (0 : Q') < w := pos_of_nonneg_not_eqv_zero hw0 hwz
    have hsum : adjCorr w N ≤
        fsum (fun a => coeffW w 1 * (coeffW w a * coeffW w a)) N := by
      unfold adjCorr
      exact fsum_mono_lt N (fun a _ => adjacent_term_le_anchor hwp hw1 a)
    have hpull :
        (fsum (fun a => coeffW w 1 * (coeffW w a * coeffW w a)) N).eqv
          (coeffW w 1 * fsum (fun a => coeffW w a * coeffW w a) N) :=
      Q'.eqv_symm (fsum_const_mul (coeffW w 1)
        (fun a => coeffW w a * coeffW w a) N)
    have hprefix : fsum (fun a => coeffW w a * coeffW w a) N
        ≤ coordNormSq w N := by
      unfold coordNormSq
      show fsum (fun a => coeffW w a * coeffW w a) N
        ≤ fsum (fun a => coeffW w a * coeffW w a) N
          + coeffW w N * coeffW w N
      exact Q'.add_le_self_of_nonneg _ _
        (Q'.mul_nonneg _ _ (coeffW_nonneg hw0 N) (coeffW_nonneg hw0 N))
    have hc1 : (0 : Q') ≤ coeffW w 1 := coeffW_nonneg hw0 1
    refine Q'.le_trans' _ _ _ hsum ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hpull) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hprefix hc1

/-- On `w≤1/2`, the anchor coefficient obeys `c₁=2w³≤w/2`. -/
theorem anchor_le_half_mul {w : Q'} (hw0 : (0 : Q') ≤ w) (hwh : w ≤ half) :
    coeffW w 1 ≤ half * w := by
  have hsq : qpow w 2 ≤ qpow half 2 := qpow_mono hw0 hwh 2
  have hmul : qpow w 2 * w ≤ qpow half 2 * w :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hsq hw0
  have hscale : Q'.ofNat 2 * (qpow w 2 * w)
      ≤ Q'.ofNat 2 * (qpow half 2 * w) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hmul (by decide)
  have hL : (coeffW w 1).eqv (Q'.ofNat 2 * (qpow w 2 * w)) := by
    change (Q'.ofNat 2 * qpow w 3).eqv
      (Q'.ofNat 2 * (qpow w 2 * w))
    exact Q'.eqv_refl _
  have hR : (Q'.ofNat 2 * (qpow half 2 * w)).eqv (half * w) := by
    have hh : (qpow half 2).eqv quarter := by decide
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _
        (Q'.mul_eqv_congr_right _ _ w hh)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 2) quarter w)) ?_
    exact Q'.mul_eqv_congr_right _ _ w
      (by decide : (Q'.ofNat 2 * quarter).eqv half)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hL)
    (Q'.le_trans' _ _ _ hscale (Q'.le_of_eqv hR))

/-- For `p=2`, the corrected bond-moving retune is exactly `(1+w)/2`. -/
theorem renormWFix_two_eqv_avg (w : Q') :
    (renormWFix 2 (by decide) w).eqv (((1 : Q') + w) * half) := by
  unfold renormWFix renormTauFix half
  have hdist : (((1 : Q') + (-w)) * Q'.mkPos 1 2 (by decide)).eqv
      ((1 : Q') * Q'.mkPos 1 2 (by decide) +
        (-w) * Q'.mkPos 1 2 (by decide)) :=
    Q'.add_mul_eqv 1 (-w) (Q'.mkPos 1 2 (by decide))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 1 _ _ (Q'.neg_eqv_congr _ _ hdist)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 1 _ _
      (Q'.neg_add_eqv ((1 : Q') * Q'.mkPos 1 2 (by decide))
        ((-w) * Q'.mkPos 1 2 (by decide)))) ?_
  have hnegmul : (-((-w) * Q'.mkPos 1 2 (by decide))).eqv
      (w * Q'.mkPos 1 2 (by decide)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _ (Q'.neg_mul_eqv w (Q'.mkPos 1 2 (by decide)))) ?_
    exact Q'.neg_neg_eqv (w * Q'.mkPos 1 2 (by decide))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 1 _ _
      (Q'.add_eqv_congr'
        (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv (Q'.mkPos 1 2 (by decide))))
        hnegmul)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.add_assoc_eqv 1 (-(Q'.mkPos 1 2 (by decide)))
        (w * Q'.mkPos 1 2 (by decide)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _
      (by decide : ((1 : Q') + -(Q'.mkPos 1 2 (by decide))).eqv
        (Q'.mkPos 1 2 (by decide)))) ?_
  exact Q'.eqv_symm
    (Q'.add_mul_eqv (1 : Q') w (Q'.mkPos 1 2 (by decide)))

/-- The explicit retune base agrees with the corrected bond-moving retune. -/
theorem retuneBase_eqv_renormWFix (w : Q') :
    (retuneBase w).eqv (renormWFix 2 (by decide) w) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv half ((1 : Q') + w)) ?_
  exact Q'.eqv_symm (renormWFix_two_eqv_avg w)

/-- The retune square dominates the original base:
`w≤((1+w)/2)²`, obtained from the constructive Bernoulli retune theorem. -/
theorem base_le_retune_square {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) :
    w ≤ qpow (retuneBase w) 2 := by
  have h := renormWFix_pow_ge_w 2 (by decide) w hw0 hw1
  have he : (qpow (retuneBase w) 2).eqv
      (qpow (renormWFix 2 (by decide) w) 2) :=
    qpow_eqv_congr_base (retuneBase_eqv_renormWFix w) 2
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.eqv_symm he))

/-- `w/2≤((1+w)/2)^3`, using `retuneBase≥1/2` and the square lemma. -/
theorem half_mul_le_retuneCube {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) :
    half * w ≤ retuneCube w := by
  have hb0 : (0 : Q') ≤ retuneBase w := by
    unfold retuneBase
    exact Q'.mul_nonneg _ _ (by decide)
      (Q'.zero_le_add _ _ (by decide) hw0)
  have hhalf : half ≤ retuneBase w := by
    unfold retuneBase
    have h1 : (1 : Q') ≤ (1 : Q') + w := Q'.add_le_self_of_nonneg 1 w hw0
    have hm := Q'.mul_le_mul_of_nonneg_left _ _ _ h1 (by decide : (0 : Q') ≤ half)
    refine Q'.le_trans' _ _ _ ?_ hm
    exact Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv half))
  have h1 : half * w ≤ retuneBase w * w :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hhalf hw0
  have h2 : retuneBase w * w ≤ retuneBase w * qpow (retuneBase w) 2 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (base_le_retune_square hw0 hw1) hb0
  refine Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 ?_)
  unfold retuneCube
  show retuneBase w * qpow (retuneBase w) 2 ≤
    (qpow (retuneBase w) 2) * retuneBase w
  exact Q'.le_of_eqv (Q'.mul_comm_eqv (retuneBase w) (qpow (retuneBase w) 2))

/-- `c₁≤((1+w)/2)^3` throughout the strong window. -/
theorem anchor_le_retuneCube {w : Q'} (hw0 : (0 : Q') ≤ w) (hwh : w ≤ half) :
    coeffW w 1 ≤ retuneCube w :=
  Q'.le_trans' _ _ _ (anchor_le_half_mul hw0 hwh)
    (half_mul_le_retuneCube hw0
      (Q'.le_trans' _ _ _ hwh (by decide : half ≤ (1 : Q'))))

/-- **Arbitrary-truncation retune inequality on the strong window.** -/
theorem arbitrary_truncation_retune {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hwh : w ≤ half) (N : Nat) :
    adjCorr w N ≤ retuneCube w * coordNormSq w N := by
  have h1 := adjCorr_le_anchor_norm hw0
    (Q'.le_trans' _ _ _ hwh (by decide : half ≤ (1 : Q'))) N
  have hnorm := coordNormSq_nonneg hw0 N
  have h2 := Q'.mul_le_mul_of_nonneg_right _ _ _
    (anchor_le_retuneCube hw0 hwh) hnorm
  exact Q'.le_trans' _ _ _ h1 h2

end YMGap.Continuum.ArbitraryTruncationRetuneCorr

#print axioms YMGap.Continuum.ArbitraryTruncationRetuneCorr.adjacent_term_le_anchor
#print axioms YMGap.Continuum.ArbitraryTruncationRetuneCorr.adjCorr_le_anchor_norm
#print axioms YMGap.Continuum.ArbitraryTruncationRetuneCorr.anchor_le_half_mul
#print axioms YMGap.Continuum.ArbitraryTruncationRetuneCorr.base_le_retune_square
#print axioms YMGap.Continuum.ArbitraryTruncationRetuneCorr.half_mul_le_retuneCube
#print axioms YMGap.Continuum.ArbitraryTruncationRetuneCorr.arbitrary_truncation_retune
