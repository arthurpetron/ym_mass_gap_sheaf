/-
All rational couplings and all finite Peter--Weyl cutoffs.

The rational projective theta certificate supplies one retained head at every
`0<w<1`; the exact projective tail estimate and PF2 supply every later term;
and cutoff quotient monotonicity supplies every earlier cutoff.  The endpoints
are closed separately: the existing strong-window theorem handles `w=0`, and
the universal Dirichlet bound handles `w=1`, where the retune cube is at least
one.  Thus no density or limiting argument is needed anywhere in `[0,1]`.
-/

import YMGap.Continuum.RationalProjectiveThetaTail
import YMGap.Continuum.CutoffRetuneBackwardPropagation
import YMGap.Continuum.HarmonicVariableAnchorRetune
import YMGap.Continuum.CharacterWindowCeiling

namespace YMGap.Continuum.RationalProjectiveRetuneAllCutoffs

set_option maxHeartbeats 4000000
set_option maxRecDepth 60000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.AllWindowCorrDirichlet
open YMGap.Continuum.CharacterWindowCeiling
open YMGap.Continuum.CutoffCorrelationMonotone
open YMGap.Continuum.CutoffRetuneBackwardPropagation
open YMGap.Continuum.EndpointCutoffTwoParameter
open YMGap.Continuum.FusedPeterWeylNormalization
open YMGap.Continuum.FusedSpectralCarrierBridge
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.HarmonicFixedTenPrefix
open YMGap.Continuum.HarmonicVariableAnchorRetune
open YMGap.Continuum.RationalProjectiveThetaHead
open YMGap.Continuum.RationalProjectiveThetaTail

local infix:50 " ≈ " => Q'.eqv

/-- The retune cube is nonnegative at every nonnegative coupling. -/
theorem retuneCube_nonnegative {w : Q'} (hw0 : (0 : Q') ≤ w) :
    (0 : Q') ≤ retuneCube w := by
  unfold retuneCube retuneBase
  exact qpow_nonneg _
    (Q'.mul_nonneg _ _ (by decide)
      (Q'.zero_le_add _ _ (by decide) hw0)) 3

/-- A nonpositive complement forces the weight above one. -/
theorem one_le_of_complement_nonpos {w : Q'}
    (h : (1 : Q') - w ≤ (0 : Q')) : (1 : Q') ≤ w := by
  have hadd := Q'.add_le_add_right ((1 : Q') - w) 0 w h
  have hleft : ((1 : Q') - w) + w ≈ (1 : Q') := by
    refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _) ?_
    exact BernsteinVariance.add_one_sub_eqv_one w
  have hright : (0 : Q') + w ≈ w := by
    rw [Q'.zero_add']
    exact Q'.eqv_refl _
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hright))

/-- If `w≥1`, the retune cube is at least one. -/
theorem one_le_retuneCube_of_one_le {w : Q'} (hw : (1 : Q') ≤ w) :
    (1 : Q') ≤ retuneCube w := by
  have hadd := Q'.add_le_add_left (1 : Q') (1 : Q') w hw
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _
    (Q'.mkPos 1 2 (by decide)) hadd (by decide)
  have hbase : (1 : Q') ≤ retuneBase w := by
    unfold retuneBase
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide)) hmul
  have hp := HeatKernelGap.qpow_mono (by decide : (0 : Q') ≤ (1 : Q')) hbase 3
  unfold retuneCube
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide)) hp

/-- The universal Dirichlet estimate closes every cutoff whenever `w≥1`,
in particular the endpoint `w=1`. -/
theorem retune_all_cutoffs_of_one_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : (1 : Q') ≤ w) (N : Nat) :
    adjCorr w N ≤ retuneCube w * coordNormSq w N := by
  have hD := adjCorr_le_coordNormSq w N
  have hnorm := coordNormSq_nonneg hw0 N
  have hm := Q'.mul_le_mul_of_nonneg_right _ _ (coordNormSq w N)
    (one_le_retuneCube_of_one_le hw) hnorm
  exact Q'.le_trans' _ _ _ hD
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv _)) hm)

/-- The rational theta head plus its PF2 tail closes every cutoff at or above
the head. -/
theorem rational_projective_all_later_cutoffs {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwp : (0 : Q') < w)
    (hu : (0 : Q') < (1 : Q') - w) (M : Nat) :
    adjCorr w (rationalThetaHead w hu + 1 + M) ≤
      retuneCube w * coordNormSq w (rationalThetaHead w hu + 1 + M) := by
  have hw1 : w ≤ (1 : Q') :=
    Q'.le_of_sub_nonneg (Q'.le_of_lt hu)
  apply fixed_anchor_all_later_cutoffs (rationalThetaHead w hu) M
    hw0 (retuneCube_nonnegative hw0)
    (rational_retained_head hw0 hwp hu)
  intro a ha
  exact anchor_step_all_tail_terms (rationalThetaHead w hu)
    hw0 hw1 hwp (rational_head_tail_step hw0 hu) (by omega)

/-- Interior rational projective closure: every finite cutoff is retune-safe
for `0<w<1`. -/
theorem rational_projective_all_cutoffs {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hwp : (0 : Q') < w)
    (hu : (0 : Q') < (1 : Q') - w) (N : Nat) :
    adjCorr w N ≤ retuneCube w * coordNormSq w N := by
  let B := rationalThetaHead w hu + 1
  have hw1 : w ≤ (1 : Q') :=
    Q'.le_of_sub_nonneg (Q'.le_of_lt hu)
  by_cases hNB : N ≤ B
  · apply retune_bound_of_later_cutoff hw0 hw1 hwp hNB
    simpa [B] using rational_projective_all_later_cutoffs hw0 hwp hu 0
  · have hBN : B ≤ N := by omega
    obtain ⟨tail, htail⟩ := Nat.le.dest hBN
    rw [← htail]
    simpa [B, Nat.add_assoc] using
      rational_projective_all_later_cutoffs hw0 hwp hu tail

/-- **All rational couplings in `[0,1]`, all finite cutoffs.** -/
theorem rational_retune_all_cutoffs {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (N : Nat) :
    adjCorr w N ≤ retuneCube w * coordNormSq w N := by
  by_cases hwp : (0 : Q') < w
  · by_cases hu : (0 : Q') < (1 : Q') - w
    · exact rational_projective_all_cutoffs hw0 hwp hu N
    · have hcomp : (1 : Q') - w ≤ (0 : Q') :=
        le_of_not_lt' hu
      have hwge : (1 : Q') ≤ w := one_le_of_complement_nonpos hcomp
      have hweq : w ≈ (1 : Q') := Q'.eqv_of_le_le hw1 hwge
      exact retune_all_cutoffs_of_one_le hw0
        (Q'.ge_of_eqv hweq) N
  · have hwle0 : w ≤ (0 : Q') := le_of_not_lt' hwp
    have hwhalf : w ≤ Q'.mkPos 1 2 (by decide) :=
      Q'.le_trans' _ _ _ hwle0 (by decide)
    exact arbitrary_truncation_retune hw0 hwhalf N

/-- Normalized fundamental Peter--Weyl form of the all-rational closure. -/
theorem rational_lamPW_all_cutoffs {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (N : Nat) :
    lamPW w N 1 ≤ retuneCube w := by
  have heq : lamPW w N 1 ≈
      Q'.divPos (adjCorr w N) (coordNormSq w N)
        (coordNormSq_pos hw0 N) :=
    Q'.eqv_trans _ _ _
      (lamPW_eq_vacNorm_p2 hw0 hw1 N 0)
      (vacNorm_fundamental_eq_ratio hw0 hw1 N)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
    (Q'.divPos_le_of_le_mul _ _ _ (rational_retune_all_cutoffs hw0 hw1 N))

end YMGap.Continuum.RationalProjectiveRetuneAllCutoffs

#print axioms YMGap.Continuum.RationalProjectiveRetuneAllCutoffs.rational_projective_all_later_cutoffs
#print axioms YMGap.Continuum.RationalProjectiveRetuneAllCutoffs.rational_projective_all_cutoffs
#print axioms YMGap.Continuum.RationalProjectiveRetuneAllCutoffs.rational_retune_all_cutoffs
#print axioms YMGap.Continuum.RationalProjectiveRetuneAllCutoffs.rational_lamPW_all_cutoffs
