/- Symbolic PF2 completion for a variable retained-head schedule. -/

import YMGap.Continuum.HarmonicSymbolicAnchorRatio
import YMGap.Continuum.HarmonicGrowingAnchorPF2

namespace YMGap.Continuum.HarmonicVariableAnchorRetune

set_option maxHeartbeats 3000000
set_option maxRecDepth 80000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CutoffCorrelationMonotone
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicFixedTenPrefix
open YMGap.Continuum.HarmonicFusedSchurObstruction
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicSymbolicAnchorRatio
open YMGap.Continuum.MultiLinkFusionDefect

local infix:50 " ≈ " => Q'.eqv

/-- A single coefficient step at an arbitrary anchor propagates, by PF2, to
every later adjacent-square term.  This is the anchor-independent tail engine
used by variable retained-head schedules. -/
theorem anchor_step_all_tail_terms {w R : Q'} (b : Nat)
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (hwp : (0 : Q') < w)
    (hstep : coeffW w (b + 1) ≤ R * coeffW w b)
    {a : Nat} (ha : b ≤ a) :
    coeffW w a * coeffW w (a + 1) ≤
      R * (coeffW w a * coeffW w a) := by
  by_cases hab : a = b
  · subst a
    have hm := Q'.mul_le_mul_of_nonneg_left _ _ (coeffW w b) hstep
      (coeffW_nonneg hw0 b)
    exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (by
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
      exact Q'.mul_assoc_eqv _ _ _))
  · have hba : b < a := Nat.lt_of_le_of_ne ha (Ne.symm hab)
    have hs := shifted_ratio_injection hw0 hw1 hwp (a := b) (N := a) hba
    have hr : coeffW w (a + 1) * coeffW w b ≤
        coeffW w a * coeffW w (b + 1) :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
        (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))
    have hsq := ratio_to_sq (coeffW_nonneg hw0 a) hr
    have hdiag0 : (0 : Q') ≤ coeffW w a * coeffW w a :=
      Q'.mul_nonneg _ _ (coeffW_nonneg hw0 a) (coeffW_nonneg hw0 a)
    have hm := Q'.mul_le_mul_of_nonneg_right _ _
      (coeffW w a * coeffW w a) hstep hdiag0
    have hchain : coeffW w b * (coeffW w a * coeffW w (a + 1)) ≤
        coeffW w b * (R * (coeffW w a * coeffW w a)) := by
      refine Q'.le_trans' _ _ _ hsq (Q'.le_trans' _ _ _ hm ?_)
      exact Q'.le_of_eqv (by
        refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left R _ _ (Q'.mul_comm_eqv _ _)) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
        exact Q'.mul_comm_eqv _ _)
    exact Q'.le_of_mul_le_mul_left hchain
      (FusionResidualBound.coeffW_pos hwp b)

/-- The exact symbolic scalar cross at `b`, together with the retained head,
closes every larger finite cutoff.  No per-anchor coefficient polynomial or
division is generated. -/
theorem variable_anchor_all_later_cutoffs {w R : Q'} (b M : Nat)
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (hwp : (0 : Q') < w)
    (hR0 : (0 : Q') ≤ R)
    (hhead : adjCorr w (b + 1) ≤ R * coordNormSq w b)
    (hcross : Q'.ofNat (b + 2) * qpow w (2 * b + 3) ≤
      R * Q'.ofNat (b + 1)) :
    adjCorr w (b + 1 + M) ≤ R * coordNormSq w (b + 1 + M) := by
  have hstep := coeffW_succ_le_of_cross b hw0 hcross
  apply fixed_anchor_all_later_cutoffs b M hw0 hR0 hhead
  intro a ha
  exact anchor_step_all_tail_terms b hw0 hw1 hwp hstep (by omega)

/-- The already-derived linear growing anchor satisfies the exact symbolic
dimension-aware scalar cross.  This strengthens the older coarse coefficient
statement and isolates the all-scale residual entirely to its retained head. -/
theorem growing_anchor_scalar_cross (k : Nat) :
    Q'.ofNat (growingAnchor k + 2) *
        qpow (harmW k) (2 * growingAnchor k + 3) ≤
      retuneCube (harmW k) * Q'.ofNat (growingAnchor k + 1) := by
  let b := growingAnchor k
  let p := qpow (harmW k) (2 * b + 3)
  change Q'.ofNat (b + 2) * p ≤
    retuneCube (harmW k) * Q'.ofNat (b + 1)
  have hnat : b + 2 ≤ 2 * (b + 1) := by omega
  have hcoef : Q'.ofNat (b + 2) ≤ Q'.ofNat (2 * (b + 1)) :=
    MovingCutoff.ofNat_le_ofNat' hnat
  have hp0 : (0 : Q') ≤ p := qpow_nonneg _ (harmW_nonneg k) _
  have hmul := Q'.mul_le_mul_of_nonneg_right _ _ p hcoef hp0
  have hleft : Q'.ofNat (2 * (b + 1)) * p ≈
      (Q'.ofNat 2 * p) * Q'.ofNat (b + 1) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ p
        (HeatKernelRGStep.ofNat_mul_eqv 2 (b + 1))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ (Q'.mul_comm_eqv _ _)) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  have hratio : Q'.ofNat 2 * p ≤ retuneCube (harmW k) := by
    dsimp only [p, b]
    exact Q'.le_trans' _ _ _ (growing_anchor_multiplier_le_eighth k)
      (eighth_le_harmonic_retune k)
  have hscale := Q'.mul_le_mul_of_nonneg_right _ _ (Q'.ofNat (b + 1))
    hratio (HeatKernelRGStep.zero_le_ofNat _)
  exact Q'.le_trans' _ _ _ hmul
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) hscale)

/-- With the scalar cross now unconditional, a proof of the single retained
head at the explicit growing schedule immediately yields every later cutoff. -/
theorem growing_anchor_retune_of_head (k M : Nat)
    (hhead : adjCorr (harmW k) (growingAnchor k + 1) ≤
      retuneCube (harmW k) * coordNormSq (harmW k) (growingAnchor k)) :
    adjCorr (harmW k) (growingAnchor k + 1 + M) ≤
      retuneCube (harmW k) *
        coordNormSq (harmW k) (growingAnchor k + 1 + M) := by
  exact variable_anchor_all_later_cutoffs (growingAnchor k) M
    (harmW_nonneg k) (harmW_le_one k) (harmW_pos k)
    (Q'.le_trans' _ _ _ (by decide) (eighth_le_harmonic_retune k))
    hhead (growing_anchor_scalar_cross k)

end YMGap.Continuum.HarmonicVariableAnchorRetune

#print axioms YMGap.Continuum.HarmonicVariableAnchorRetune.anchor_step_all_tail_terms
#print axioms YMGap.Continuum.HarmonicVariableAnchorRetune.variable_anchor_all_later_cutoffs
#print axioms YMGap.Continuum.HarmonicVariableAnchorRetune.growing_anchor_scalar_cross
#print axioms YMGap.Continuum.HarmonicVariableAnchorRetune.growing_anchor_retune_of_head
