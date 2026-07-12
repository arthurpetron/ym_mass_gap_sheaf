/-
`FusedPeterWeylNormalization` — Phase 14.3 normalization audit and correction.

`FusedRatioCorridor.lamB = boxSum(s)/boxSum(0)` is the vacuum-normalized
CHARACTER coefficient.  It is not yet the transfer EIGENVALUE: the real
Peter–Weyl shared-link integral contributes `1/dim_s`.  This module installs
that factor, proves the corrected corridor, and banks a closed-rational
refutation of identifying the old `lamB` with the physical eigenvalue.

For the fundamental channel the correction is exact:

  * free character corridor center `2 * coeffW(w,1) = 4 w^3`
    becomes the eigenvalue center `2 w^3`;
  * interacting width `intAmp(3,1) w^6 = 36 w^6`
    becomes `18 w^6`;
  * on `0 <= w <= 1/2`, the corrected erosion budget closes with
    `delta(w) = 3 w^3`, replacing the uncorrected `41 w^3` certificate.

This is a strict correction/advance of the finite character normalization.
It does not solve the remaining rescaled AF-tail identification: even the
corrected two-copy free center `2 w^3` reaches one before `w = 1`, so the
continuum recursion must still be expressed at the retuned next-scale weight.

Constructive contract: pure `Q'`/`Nat`, exact finite character sums and the
proved Peter–Weyl kernel; no `Classical`, `Real`, `native_decide`, or holes.
-/

import YMGap.Continuum.UniformWidthMargin
import YMGap.Continuum.PeterWeylRealWeight

namespace YMGap.Continuum.FusedPeterWeylNormalization

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusedChannelAll
open YMGap.Continuum.FusedChannelOne
open YMGap.Continuum.FusedFreeSplit
open YMGap.Continuum.FusedRatioCorridor
open YMGap.Continuum.IntAmpAnchors
open YMGap.Continuum.MarginErosionBrick
open YMGap.Continuum.PeterWeylRealWeight
open YMGap.Continuum.UniformWidthMargin

/-! ## 1. The physical Peter–Weyl-normalized blocked eigenvalue -/

/-- The vacuum-normalized blocked transfer EIGENVALUE: the character ratio
`lamB` times the real shared-link factor `1/dim_s`. -/
def lamPW (w : Q') (N s : Nat) : Q' :=
  lamB w N s * haarSubKernel s s

/-- On every excited channel, `lamB` is exactly `dim_s` times `lamPW`.
Thus `lamB` is the vacuum-normalized CHARACTER rate, while `lamPW` is the
Peter–Weyl transfer eigenvalue. -/
theorem lamB_is_dim_times_lamPW (w : Q') (N k : Nat) :
    (dimQ (k + 1) * lamPW w N (k + 1)).eqv (lamB w N (k + 1)) := by
  unfold lamPW
  rw [haarSubKernel_diag_excited]
  have hOne : ((1 : Q') * Q'.invSucc (k + 1)).eqv (Q'.invSucc (k + 1)) :=
    Q'.one_mul_eqv _
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (dimQ (k + 1)) _ _
      (Q'.mul_eqv_congr_left (lamB w N (k + 1)) _ _ hOne)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv (dimQ (k + 1)) (lamB w N (k + 1))
        (Q'.invSucc (k + 1)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (Q'.invSucc (k + 1))
      (Q'.mul_comm_eqv (dimQ (k + 1)) (lamB w N (k + 1)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv (lamB w N (k + 1)) (dimQ (k + 1))
      (Q'.invSucc (k + 1))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (lamB w N (k + 1)) _ _
      (Q'.ofNat_succ_mul_invSucc (k + 1))) ?_
  exact Q'.mul_one_eqv _

/-- **Machine-checked normalization refutation.** At the pilot anchor the
old `lamB` is not the Peter–Weyl eigenvalue `lamPW`; the omitted factor is
the nontrivial fundamental dimension `dim_1 = 2`. -/
theorem lamB_not_lamPW_anchor :
    ¬ (lamB w0 3 1).eqv (lamPW w0 3 1) := by decide

/-- **UV-tail fence for the old normalization.** At `w = 9/10`, the
vacuum-normalized character ratio is already greater than one.  It therefore
cannot itself occupy the eigenvalue slot of a normalized positive transfer
contraction; the Peter–Weyl `1/dim` correction is mandatory. -/
theorem lamB_uv_tail_not_le_one :
    ¬ (lamB wTail 3 1 ≤ (1 : Q')) := by decide

/-! ## 2. The corrected exact corridor -/

/-- Multiplying the character corridor by the nonnegative Peter–Weyl
factor gives the physical eigenvalue corridor.  Its free terms collapse
from character coefficients to `physLinkWeight` by the exact `delta/dim`
orthogonality identity. -/
theorem lamPW_corridor {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    {N k : Nat} (hchan : k + 1 ≤ N) :
    lamPW w N (k + 1) ≤
      (physLinkWeight w (k + 1) + physLinkWeight w (k + 1))
        + (intAmp N (k + 1) * qpow w 6) * haarSubKernel (k + 1) (k + 1) := by
  have hcorr := lamB_corridor hw0 hw1 (Nat.succ_le_succ (Nat.zero_le k)) hchan
  have hK0 : (0 : Q') ≤ haarSubKernel (k + 1) (k + 1) := by
    rw [haarSubKernel_diag_excited]
    exact Q'.mul_nonneg _ _ (by decide) (Q'.invSucc_nonneg (k + 1))
  have hmul := Q'.mul_le_mul_of_nonneg_right _ _ _ hcorr hK0
  unfold lamPW
  refine Q'.le_trans' _ _ _ hmul ?_
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_mul_eqv
      (coeffW w (k + 1) + coeffW w (k + 1))
      (intAmp N (k + 1) * qpow w 6)
      (haarSubKernel (k + 1) (k + 1))) ?_
  refine Q'.add_eqv_congr' ?_ (Q'.eqv_refl _)
  refine Q'.eqv_trans _ _ _
    (Q'.add_mul_eqv (coeffW w (k + 1)) (coeffW w (k + 1))
      (haarSubKernel (k + 1) (k + 1))) ?_
  exact Q'.add_eqv_congr'
    (restored_link_amplitude w k) (restored_link_amplitude w k)

/-- Fundamental-channel specialization: center `2 w^3`, derived width
`36 w^6 / 2`. -/
theorem lamPW_fund_corridor {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    lamPW w 3 1 ≤
      (physLinkWeight w 1 + physLinkWeight w 1)
        + (intAmp 3 1 * qpow w 6) * haarSubKernel 1 1 :=
  lamPW_corridor hw0 hw1 (by omega : 0 + 1 ≤ 3)

/-! ## 3. The corrected strong-window budget -/

/-- The corrected fundamental interacting width is exactly `18 w^6`:
the derived character amplitude `36` times the Peter–Weyl factor `1/2`. -/
theorem fund_width_eq (w : Q') :
    ((intAmp 3 1 * qpow w 6) * haarSubKernel 1 1).eqv
      (Q'.ofNat 18 * qpow w 6) := by
  rw [haarSubKernel_diag_excited]
  have hAmp : (intAmp 3 1).eqv (Q'.ofNat 36) := intAmp_N3_ch1
  have hK : ((1 : Q') * Q'.invSucc 1).eqv (Q'.invSucc 1) := Q'.one_mul_eqv _
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hAmp)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat 36 * qpow w 6) _ _ hK) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv (Q'.ofNat 36) (qpow w 6) (Q'.invSucc 1)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat 36) _ _
      (Q'.mul_comm_eqv (qpow w 6) (Q'.invSucc 1))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv (Q'.ofNat 36) (Q'.invSucc 1) (qpow w 6))) ?_
  exact Q'.mul_eqv_congr_right _ _ (qpow w 6)
    (by decide : (Q'.ofNat 36 * Q'.invSucc 1).eqv (Q'.ofNat 18))

/-- The Peter–Weyl correction halves the derived channel-1 amplitude from
`36` to `18`, but `18` still exceeds the old global `Sum ≤ 6` certificate.
Thus `1/dim` fixes the spectral normalization without pretending to close the
superseded continuum-end raw-amplitude budget. -/
theorem pw_intAmp_still_exceeds_six :
    ¬ (intAmp 3 1 * haarSubKernel 1 1 ≤ Q'.ofNat 6) := by decide

/-- For `0 ≤ w ≤ 1/2`, the correctly normalized derived width obeys

`18 w^6 ≤ (3 w^3) * (1 - 2 w^3)`.

Thus the Peter–Weyl erosion rate is `delta(w) = 3 w^3`, versus the old
character-rate certificate `41 w^3`. -/
theorem pw_uniform_width_le_margin {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hwh : w ≤ half) :
    (intAmp 3 1 * qpow w 6) * haarSubKernel 1 1
      ≤ (Q'.ofNat 3 * qpow w 3)
          * ((1 : Q') + -(physLinkWeight w 1 + physLinkWeight w 1)) := by
  have h8 : qpow w 3 ≤ eighth := qpow3_le_eighth hw0 hwh
  have hq3 : (0 : Q') ≤ qpow w 3 := qpow_nonneg w hw0 3
  let q94 : Q' := Q'.mkPos 9 4 (by omega)
  let q34 : Q' := Q'.mkPos 3 4 (by omega)
  have hL : (intAmp 3 1 * qpow w 6) * haarSubKernel 1 1
      ≤ q94 * qpow w 3 := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (fund_width_eq w)) ?_
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left (Q'.ofNat 18) _ _ (qpow_add' w 3 3))) ?_
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ h8 hq3)
        (by decide : (0 : Q') ≤ Q'.ofNat 18)) ?_
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv (Q'.ofNat 18) eighth (qpow w 3)))) ?_
    exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (by decide : Q'.ofNat 18 * eighth ≤ q94) hq3
  have hfree : physLinkWeight w 1 + physLinkWeight w 1
      ≤ Q'.mkPos 1 4 (by omega) := by
    show qpow w 3 + qpow w 3 ≤ Q'.mkPos 1 4 (by omega)
    refine Q'.le_trans' _ _ _ (Q'.add_le_add h8 h8) ?_
    exact by decide
  have hm : q34 ≤
      (1 : Q') + -(physLinkWeight w 1 + physLinkWeight w 1) := by
    refine Q'.le_trans' _ _ _
      (by decide : q34 ≤ (1 : Q') + -(Q'.mkPos 1 4 (by omega))) ?_
    exact Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hfree)
  have h3 : (0 : Q') ≤ Q'.ofNat 3 * qpow w 3 :=
    Q'.mul_nonneg _ _ (by decide) hq3
  refine Q'.le_trans' _ _ _ hL ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv ?_)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hm h3)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (qpow w 3)
      (Q'.eqv_symm (by decide : (Q'.ofNat 3 * q34).eqv q94))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv (Q'.ofNat 3) q34 (qpow w 3)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat 3) _ _
      (Q'.mul_comm_eqv q34 (qpow w 3))) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 3) (qpow w 3) q34)

/-- The corrected fundamental recursion throughout the strong window. -/
theorem pw_window_recursion {w : Q'} (hw0 : (0 : Q') ≤ w) (hwh : w ≤ half) :
    ((1 : Q') - Q'.ofNat 3 * qpow w 3)
        * ((1 : Q') + -(physLinkWeight w 1 + physLinkWeight w 1))
      ≤ (1 : Q') + -(lamPW w 3 1) :=
  margin_recursion_of_corridor
    (Q'.eqv_refl _) (Q'.eqv_refl _)
    (lamPW_fund_corridor hw0 (Q'.le_trans' _ _ _ hwh (by decide)))
    (pw_uniform_width_le_margin hw0 hwh)

/-- Even after the mandatory `1/dim` correction, the two genuine free
pairings give center `2 w^3`, whose same-scale margin is negative at `w=9/10`.
So the correction does not erase the remaining retuned-next-scale obligation. -/
theorem pw_two_pair_margin_negative_at_tail :
    ¬ ((0 : Q') ≤
      (1 : Q') + -(physLinkWeight wTail 1 + physLinkWeight wTail 1)) := by decide

end YMGap.Continuum.FusedPeterWeylNormalization

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.FusedPeterWeylNormalization.lamB_is_dim_times_lamPW
#print axioms YMGap.Continuum.FusedPeterWeylNormalization.lamB_not_lamPW_anchor
#print axioms YMGap.Continuum.FusedPeterWeylNormalization.lamB_uv_tail_not_le_one
#print axioms YMGap.Continuum.FusedPeterWeylNormalization.lamPW_corridor
#print axioms YMGap.Continuum.FusedPeterWeylNormalization.fund_width_eq
#print axioms YMGap.Continuum.FusedPeterWeylNormalization.pw_intAmp_still_exceeds_six
#print axioms YMGap.Continuum.FusedPeterWeylNormalization.pw_uniform_width_le_margin
#print axioms YMGap.Continuum.FusedPeterWeylNormalization.pw_window_recursion
#print axioms YMGap.Continuum.FusedPeterWeylNormalization.pw_two_pair_margin_negative_at_tail
