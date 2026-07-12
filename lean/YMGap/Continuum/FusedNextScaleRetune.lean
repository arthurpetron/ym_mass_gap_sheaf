/-
`FusedNextScaleRetune` — the exact next-scale margin orientation, without
the false same-scale proxy.

The corrected fused eigenvalue is already identified exactly with the
vacuum-normalized `p=2` bond-moved eigenvalue by
`FusedSpectralCarrierBridge.lamPW_eq_vacNorm_p2`.  This module proves the
remaining scale arithmetic uniformly on the whole physical window:

  1 - w^3 <= 2 * (1 - renormWFix(2,w)^3).

Combining it with the existing exact vacuum-normalized defect comparison gives,
for every truncation `N` and every excited channel,

  1 - w^3 <= 2 * ((1 - lamPW(w,N,s)) + normEigShift(w,N,s)).

Thus truncation growth is not needed for this defect-inclusive next-scale
comparison.  Removing `normEigShift` is the genuine fusion/local-CLT question;
it is not assumed here.  On the strong window, the independent arbitrary-`N`
correlation theorem `ArbitraryTruncationRetuneCorr.arbitrary_truncation_retune`
already proves the exact numerator/denominator cross inequality.  Extending its
defect-free correlation proof from `w <= 1/2` to all `w <= 1` is the sharply
identified residual, not a new frontier field.

The factor two is the algebraic `p=2` block scale.  Identifying it with the
actual physical lattice-spacing law and `massLat/spacing` sequence remains a
separate pin; no frontier carrier is inhabited here.
-/

import YMGap.Continuum.FusedSpectralCarrierBridge
import YMGap.Continuum.ArbitraryTruncationRetuneCorr
import YMGap.Continuum.FusedAmplitudeDerivation

namespace YMGap.Continuum.FusedNextScaleRetune

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingRetuneFix
open YMGap.Continuum.BondMovingRelResidual
open YMGap.Continuum.FusedAmplitudeDerivation
open YMGap.Continuum.FusedPeterWeylNormalization
open YMGap.Continuum.FusedSpectralCarrierBridge
open YMGap.Continuum.PeterWeylRealWeight
open YMGap.Continuum.VacNormEigShift
open YMGap.Continuum.ArbitraryTruncationRetuneCorr

/-! ## 1. Exact scale arithmetic -/

/-- Geometric sums are monotone in a nonnegative base. -/
theorem geomSum_mono_base {x y : Q'} (hx : (0 : Q') ≤ x) (hxy : x ≤ y) :
    ∀ n, geomSum x n ≤ geomSum y n
  | 0 => Q'.le_refl' 0
  | n + 1 =>
      Q'.add_le_add (geomSum_mono_base hx hxy n) (qpow_mono_base hx hxy n)

/-- Exact identity `1 - renormWFix = renormTauFix`. -/
theorem one_sub_renormWFix_eqv_tau (p : Nat) (hp : 0 < p) (w : Q') :
    ((1 : Q') - renormWFix p hp w).eqv (renormTauFix p hp w) := by
  show ((1 : Q') + -((1 : Q') + (-(renormTauFix p hp w)))).eqv
    (renormTauFix p hp w)
  have ha : (-((1 : Q') + (-(renormTauFix p hp w)))).eqv
      ((-1 : Q') + renormTauFix p hp w) := by
    refine Q'.eqv_trans _ _ _
      (Q'.neg_add_eqv (1 : Q') (-(renormTauFix p hp w))) ?_
    exact Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv (renormTauFix p hp w))
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left 1 _ _ ha) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (1 : Q') (-1) (renormTauFix p hp w))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (Q'.add_neg_self_eqv (1 : Q'))) ?_
  exact QPoly.q_zero_add_eqv _

/-- At `p=2`, twice the retuned base margin is exactly the original base
margin: `2 * (1-r) = 1-w`. -/
theorem twice_retuned_base_margin (w : Q') :
    (Q'.ofNat 2 * ((1 : Q') - renormWFix 2 (by omega) w)).eqv
      ((1 : Q') - w) := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _
      (one_sub_renormWFix_eqv_tau 2 (by omega) w)) ?_
  unfold renormTauFix
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _
      (Q'.mul_comm_eqv ((1 : Q') - w) (Q'.mkPos 1 2 (by omega)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv (Q'.ofNat 2) (Q'.mkPos 1 2 (by omega)) ((1 : Q') - w))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ ((1 : Q') - w)
      (by decide : (Q'.ofNat 2 * Q'.mkPos 1 2 (by omega)).eqv (1 : Q'))) ?_
  exact Q'.one_mul_eqv _

/-- **Uniform next-scale free-margin comparison.** -/
theorem free_margin_le_twice_retuned {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) :
    (1 : Q') - physLinkWeight w 1 ≤
      Q'.ofNat 2 *
        ((1 : Q') - physLinkWeight (renormWFix 2 (by omega) w) 1) := by
  let r := renormWFix 2 (by omega) w
  have hwr : w ≤ r := w_le_renormWFix hw0 hw1 2 (by omega)
  have hgeom : geomSum w 3 ≤ geomSum r 3 := geomSum_mono_base hw0 hwr 3
  have hsub : (0 : Q') ≤ (1 : Q') - w := Q'.sub_nonneg_of_le hw1
  have hmul : ((1 : Q') - w) * geomSum w 3 ≤
      ((1 : Q') - w) * geomSum r 3 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hgeom hsub
  have hfacW : ((1 : Q') - physLinkWeight w 1).eqv
      (((1 : Q') - w) * geomSum w 3) := oneSub_pow_factor w 3
  have hfacR : ((1 : Q') - physLinkWeight r 1).eqv
      (((1 : Q') - r) * geomSum r 3) := oneSub_pow_factor r 3
  have htarget : (((1 : Q') - w) * geomSum r 3).eqv
      (Q'.ofNat 2 * ((1 : Q') - physLinkWeight r 1)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (geomSum r 3)
        (Q'.eqv_symm (twice_retuned_base_margin w))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (Q'.ofNat 2) ((1 : Q') - r) (geomSum r 3)) ?_
    exact Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ (Q'.eqv_symm hfacR)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfacW)
    (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv htarget))

/-! ## 2. Exact arbitrary-truncation next-scale erosion -/

/-- **The defect-inclusive next-scale comparison, arbitrary truncation and
channel.** The incoming free fundamental margin is controlled by twice the
outgoing corrected fused margin plus the exact vacuum-normalized spectral
defect.  No truncation-dependent hypothesis is used. -/
theorem rescaled_margin_with_exact_defect {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (N k : Nat) :
    (1 : Q') - physLinkWeight w 1 ≤
      Q'.ofNat 2 *
        (((1 : Q') - lamPW w N (k + 1)) +
          normEigShift N 2 (by decide) hw0 hw1 (k + 1)) := by
  have herode := fused_margin_after_retuned_erosion hw0 hw1 N k
  have hadd :
      (1 : Q') - physLinkWeight (renormWFix 2 (by decide) w) (k + 1) ≤
        ((1 : Q') - lamPW w N (k + 1)) +
          normEigShift N 2 (by decide) hw0 hw1 (k + 1) :=
    EigenvalueShiftBridge.le_add_of_sub_le herode
  have hfund :
      (1 : Q') - physLinkWeight (renormWFix 2 (by decide) w) 1 ≤
        (1 : Q') - physLinkWeight (renormWFix 2 (by decide) w) (k + 1) := by
    have hr0 := renormWFix_nonneg hw0 2 (by decide)
    have hr1 := renormWFix_le_one hw1 2 (by decide)
    have heig : physLinkWeight (renormWFix 2 (by decide) w) (k + 1) ≤
        physLinkWeight (renormWFix 2 (by decide) w) 1 :=
      FusedChannelOne.qpow_exp_antitone hr0 hr1
        (BondMovingMoment.c4_mono (Nat.succ_le_succ (Nat.zero_le k)))
    show (1 : Q') + -(physLinkWeight (renormWFix 2 (by decide) w) 1) ≤
      (1 : Q') + -(physLinkWeight (renormWFix 2 (by decide) w) (k + 1))
    exact Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg heig)
  refine Q'.le_trans' _ _ _ (free_margin_le_twice_retuned hw0 hw1) ?_
  exact Q'.mul_le_mul_of_nonneg_left _ _ _
    (Q'.le_trans' _ _ _ hfund hadd) (by decide)

/-- The already-proved arbitrary-cutoff correlation comparison on the strong
window, re-exposed at the next-scale module boundary. -/
theorem arbitrary_truncation_strong_window {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hwh : w ≤ Q'.mkPos 1 2 (by decide)) (N : Nat) :
    adjCorr w N ≤ retuneCube w * coordNormSq w N :=
  arbitrary_truncation_retune hw0 hwh N

end YMGap.Continuum.FusedNextScaleRetune

#print axioms YMGap.Continuum.FusedNextScaleRetune.geomSum_mono_base
#print axioms YMGap.Continuum.FusedNextScaleRetune.one_sub_renormWFix_eqv_tau
#print axioms YMGap.Continuum.FusedNextScaleRetune.twice_retuned_base_margin
#print axioms YMGap.Continuum.FusedNextScaleRetune.free_margin_le_twice_retuned
#print axioms YMGap.Continuum.FusedNextScaleRetune.rescaled_margin_with_exact_defect
#print axioms YMGap.Continuum.FusedNextScaleRetune.arbitrary_truncation_strong_window
