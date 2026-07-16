/-
Defect-free fundamental next-scale comparison.

The full rational projective theorem proves that the normalized fundamental
fused eigenvalue is bounded directly by the `p=2` retuned heat-kernel
eigenvalue, at every finite cutoff and every rational coupling in `[0,1]`.
Consequently the `normEigShift` erosion carried by the general-channel bridge
is unnecessary in the fundamental channel.  Combining this with the exact
factor-two retune arithmetic gives a defect-free next-scale margin inequality.
-/

import YMGap.Continuum.RationalProjectiveRetuneAllCutoffs
import YMGap.Continuum.FusedNextScaleRetune

namespace YMGap.Continuum.FusedFundamentalDefectFreeRetune

set_option maxHeartbeats 2000000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingRelResidual
open YMGap.Continuum.BondMovingRetuneFix
open YMGap.Continuum.EigenvalueShiftBridge
open YMGap.Continuum.FusedNextScaleRetune
open YMGap.Continuum.FusedPeterWeylNormalization
open YMGap.Continuum.PeterWeylRealWeight
open YMGap.Continuum.RationalProjectiveRetuneAllCutoffs

local infix:50 " ≈ " => Q'.eqv

/-- The cubic retune is exactly the fundamental eigenvalue of the corrected
`p=2` heat-kernel transfer. -/
theorem retuneCube_eqv_retuned_fundamental (w : Q') :
    retuneCube w ≈
      physLinkWeight (renormWFix 2 (by decide) w) 1 := by
  unfold retuneCube physLinkWeight
  have h := BondMovingRelResidual.qpow_eqv_congr_base
    (retuneBase_eqv_renormWFix w) 3
  simpa [c4] using h

/-- Full-window, arbitrary-cutoff spectral comparison with no additive shift
in the fundamental channel. -/
theorem lamPW_le_retuned_fundamental {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (N : Nat) :
    lamPW w N 1 ≤ physLinkWeight (renormWFix 2 (by decide) w) 1 := by
  exact Q'.le_trans' _ _ _ (rational_lamPW_all_cutoffs hw0 hw1 N)
    (Q'.le_of_eqv (retuneCube_eqv_retuned_fundamental w))

/-- The retuned free fundamental margin is below the actual fused fundamental
margin, with zero `normEigShift` erosion. -/
theorem retuned_margin_le_fused_margin {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (N : Nat) :
    (1 : Q') - physLinkWeight (renormWFix 2 (by decide) w) 1 ≤
      (1 : Q') - lamPW w N 1 := by
  exact Q'.add_le_add_left 1 _ _
    (Q'.neg_le_neg (lamPW_le_retuned_fundamental hw0 hw1 N))

/-- **Defect-free fundamental next-scale comparison.**  The factor two is the
exact `p=2` scale arithmetic; no spectral-shift term remains. -/
theorem fundamental_rescaled_margin_defect_free {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (N : Nat) :
    (1 : Q') - physLinkWeight w 1 ≤
      Q'.ofNat 2 * ((1 : Q') - lamPW w N 1) := by
  refine Q'.le_trans' _ _ _ (free_margin_le_twice_retuned hw0 hw1) ?_
  exact Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2)
    (retuned_margin_le_fused_margin hw0 hw1 N) (by decide)

/-- Harmonic specialization, uniform in the finite cutoff. -/
theorem harmonic_fundamental_rescaled_margin (k N : Nat) :
    (1 : Q') - physLinkWeight (HarmonicCutoffBoundary.harmW k) 1 ≤
      Q'.ofNat 2 *
        ((1 : Q') - lamPW (HarmonicCutoffBoundary.harmW k) N 1) :=
  fundamental_rescaled_margin_defect_free
    (HarmonicCutoffBoundary.harmW_nonneg k)
    (HarmonicCutoffBoundary.harmW_le_one k) N

end YMGap.Continuum.FusedFundamentalDefectFreeRetune

#print axioms YMGap.Continuum.FusedFundamentalDefectFreeRetune.retuneCube_eqv_retuned_fundamental
#print axioms YMGap.Continuum.FusedFundamentalDefectFreeRetune.lamPW_le_retuned_fundamental
#print axioms YMGap.Continuum.FusedFundamentalDefectFreeRetune.retuned_margin_le_fused_margin
#print axioms YMGap.Continuum.FusedFundamentalDefectFreeRetune.fundamental_rescaled_margin_defect_free
#print axioms YMGap.Continuum.FusedFundamentalDefectFreeRetune.harmonic_fundamental_rescaled_margin
