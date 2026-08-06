/-
Track 11.7-fusion / R2q -- refined-reference compiler for the physical square gap.

The additive-gap compiler reduces the physical defect product to an estimate on

    fine^2 - coarse.

Direct evaluation of those cutoff-dependent rational powers is unnecessary.
For values in `[0,1]`, squaring is two-Lipschitz.  Consequently the physical
mode-one gap is bounded by the corresponding refined-retune gap plus the
already-defined finite-cutoff spectral defects:

    fine^2 - coarse
      <= (refFine^2 - refCoarse) + 2*fineDefect + coarseDefect.

This is a proof-about-computation interface: later work may bound the small
refined reference expression symbolically and reuse the existing
`normEigShift2` cutoff modulus.  No physical fusion quotient or large integer
cross product is evaluated here.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2RetunedFusionAdditiveGap
import YMGap.Continuum.CutoffTailRefinedCarrier

namespace YMGap.Continuum.P2RetunedFusionReferenceGap

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingRetuneFix
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.ContinuumYMStack
open YMGap.Continuum.CutoffTailRefinedCarrier
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.P2RetunedBlockingDictionary
open YMGap.Continuum.P2RetunedFusionPowerCertificate
open YMGap.Continuum.P2RetunedFusionPhysicalMode
open YMGap.Continuum.P2RetunedRatioCompiler
open YMGap.Continuum.RefinedRetune

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic proof-about-computation algebra -/

/-- Difference-of-squares factorization in the `Q'` setoid. -/
theorem square_sub_square_eqv (x r : Q') :
    (x * x + -(r * r)) ≈ (x + -r) * (x + r) := by
  have hleft : x * (x + r) ≈ x * x + x * r :=
    Q'.mul_add_eqv x x r
  have hright : (-r) * (x + r) ≈ -(x * r) + -(r * r) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (-r) x r) ?_
    refine Q'.add_eqv_congr' ?_ ?_
    · exact Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv r x)
        (Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv r x))
    · exact Q'.neg_mul_eqv r r
  have hexpand :
      (x + -r) * (x + r) ≈
        (x * x + x * r) + (-(x * r) + -(r * r)) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv x (-r) (x + r)) ?_
    exact Q'.add_eqv_congr' hleft hright
  have hswap :
      (x * x + x * r) + (-(x * r) + -(r * r)) ≈
        (x * x + -(r * r)) + (x * r + -(x * r)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (x * x + x * r) _ _
        (Q'.add_comm_eqv (-(x * r)) (-(r * r)))) ?_
    exact Q'.add_swap_inner (x * x) (x * r) (-(r * r)) (-(x * r))
  have hcancel :
      (x * x + -(r * r)) + (x * r + -(x * r)) ≈
        x * x + -(r * r) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (x * x + -(r * r)) _ _
        (Q'.add_neg_self_eqv (x * r))) ?_
    rw [Q'.add_zero']
    exact Q'.eqv_refl _
  exact Q'.eqv_symm
    (Q'.eqv_trans _ _ _ hexpand (Q'.eqv_trans _ _ _ hswap hcancel))

/-- On `[0,1]`, squaring is two-Lipschitz in the one-sided form needed by
the physical power gap. -/
theorem square_sub_square_le_two_abs
    {x r e : Q'} (hx0 : (0 : Q') <= x) (hx1 : x <= (1 : Q'))
    (hr0 : (0 : Q') <= r) (hr1 : r <= (1 : Q'))
    (he : absQ (x + -r) <= e) :
    x * x + -(r * r) <= Q'.ofNat 2 * e := by
  have he0 : (0 : Q') <= e :=
    Q'.le_trans' _ _ _ (absQ_nonneg (x + -r)) he
  have hdiff : x + -r <= e :=
    Q'.le_trans' _ _ _ (le_absQ (x + -r)) he
  have hsum0 : (0 : Q') <= x + r := Q'.zero_le_add x r hx0 hr0
  have hsum1 : x + r <= Q'.ofNat 2 := by
    exact Q'.le_trans' _ _ _ (Q'.add_le_add hx1 hr1) (Q'.le_of_eqv (by decide))
  have hfirst : (x + -r) * (x + r) <= e * (x + r) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hdiff hsum0
  have hsecond : e * (x + r) <= e * Q'.ofNat 2 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hsum1 he0
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (square_sub_square_eqv x r))
    (Q'.le_trans' _ _ _ hfirst
      (Q'.le_trans' _ _ _ hsecond
        (Q'.le_of_eqv (Q'.mul_comm_eqv e (Q'.ofNat 2)))))

/-- `absQ` is symmetric under swapping the two arguments of a difference. -/
theorem absQ_sub_comm_eqv (x r : Q') :
    absQ (r + -x) ≈ absQ (x + -r) := by
  have hneg : r + -x ≈ -(x + -r) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv r (-x)) ?_
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv x (-r)) ?_
    exact Q'.add_eqv_congr_left (-x) _ r (Q'.neg_neg_eqv r)
  refine Q'.eqv_trans _ _ _ (absQ_eqv_congr hneg) ?_
  refine Q'.eqv_trans _ _ _ (absQ_eqv_abs (-(x + -r))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.abs_neg' (x + -r)) ?_
  exact Q'.eqv_symm (absQ_eqv_abs (x + -r))

/-- Additive telescope: a fine-side error and a coarse-side error transport a
reference gap to the physical gap. -/
theorem gap_le_reference_gap_add_errors
    {fine refFine coarse refCoarse fineError coarseError : Q'}
    (hfine : fine + -refFine <= fineError)
    (hcoarse : refCoarse + -coarse <= coarseError) :
    fine + -coarse <=
      (refFine + -refCoarse) + (fineError + coarseError) := by
  have hfineUp : fine <= refFine + fineError := by
    have h := Q'.add_le_add_right _ _ refFine hfine
    have hleft : fine ≈ (fine + -refFine) + refFine :=
      Q'.eqv_trans _ _ _ (Q'.add_sub_cancel_eqv fine refFine)
        (Q'.add_comm_eqv refFine (fine + -refFine))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ h
        (Q'.le_of_eqv (Q'.add_comm_eqv fineError refFine)))
  have hcoarseNeg : -coarse <= -refCoarse + coarseError := by
    have h := Q'.add_le_add_right _ _ (-refCoarse) hcoarse
    have hleft :
        (refCoarse + -coarse) + -refCoarse ≈ -coarse := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv refCoarse (-coarse) (-refCoarse)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left refCoarse _ _
          (Q'.add_comm_eqv (-coarse) (-refCoarse))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv refCoarse (-refCoarse) (-coarse))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (-coarse)
          (Q'.add_neg_self_eqv refCoarse)) ?_
      rw [Q'.zero_add']
      exact Q'.eqv_refl _
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hleft))
      (Q'.le_trans' _ _ _ h
        (Q'.le_of_eqv (Q'.add_comm_eqv coarseError (-refCoarse))))
  have hadd := Q'.add_le_add hfineUp hcoarseNeg
  exact Q'.le_trans' _ _ _ hadd
    (Q'.le_of_eqv
      (Q'.add_swap_inner refFine fineError (-refCoarse) coarseError))

/-- Combining the preceding two lemmas transports a square gap through two
absolute spectral-error bounds. -/
theorem squareGap_le_referenceSquareGap_add_errors
    {fine refFine coarse refCoarse fineError coarseError : Q'}
    (hfine0 : (0 : Q') <= fine) (hfine1 : fine <= (1 : Q'))
    (hrefFine0 : (0 : Q') <= refFine) (hrefFine1 : refFine <= (1 : Q'))
    (hfineError : absQ (fine + -refFine) <= fineError)
    (hcoarseError : absQ (coarse + -refCoarse) <= coarseError) :
    fine * fine + -coarse <=
      (refFine * refFine + -refCoarse) +
        (Q'.ofNat 2 * fineError + coarseError) := by
  have hf := square_sub_square_le_two_abs hfine0 hfine1
    hrefFine0 hrefFine1 hfineError
  have hc : refCoarse + -coarse <= coarseError :=
    Q'.le_trans' _ _ _
      (le_absQ (refCoarse + -coarse))
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (absQ_sub_comm_eqv coarse refCoarse)) hcoarseError)
  exact gap_le_reference_gap_add_errors hf hc

/-! ## 2. The physical p=2 mode-one specialization -/

/-- Refined retune reference for the physical mode-one separator. -/
def refinedModeOneQ (F : P2RetunedControlFamily) (k : Nat) : Q' :=
  retEig2 2 (by decide) (refineCoeff 2 (by decide)) (F.w k) 1

/-- Exact physical-to-refined spectral defect at mode one. -/
def modeOneRefinedDefect (F : P2RetunedControlFamily) (k : Nat) : Q' :=
  normEigShift2 (F.N k) 2 (by decide) (F.hw0 k) (F.hw1 k)
    (refineCoeff 2 (by decide)) 1

/-- The spectrum-selected mode-one rational is the existing vacuum-normalized
physical eigenvalue. -/
theorem fusionModeOne_eqv_p2VacNorm (F : P2RetunedControlFamily) (k : Nat) :
    fusionModeQ F modeOne k ≈
      p2VacNorm (F.N k) (F.hw0 k) (F.hw1 k) 1 := by
  simpa only [fusionModeQ, modeOne, P2RetunedControlFamily.control] using
    (fusionEig_eqv_p2VacNorm (F.N k) (F.hw0 k) (F.hw1 k) 1)

/-- The named defect is literally the absolute physical/reference difference. -/
theorem fusionModeOne_abs_refined_eqv_defect
    (F : P2RetunedControlFamily) (k : Nat) :
    absQ (fusionModeQ F modeOne k + -refinedModeOneQ F k) ≈
      modeOneRefinedDefect F k := by
  unfold refinedModeOneQ modeOneRefinedDefect normEigShift2
  apply absQ_eqv_congr
  exact Q'.add_eqv_congr_right _ _ _ (fusionModeOne_eqv_p2VacNorm F k)

/-- The physical mode-one eigenvalue lies in `[0,1]` at every compiled cutoff. -/
theorem fusionModeOne_range (F : P2RetunedControlFamily) (k : Nat) :
    ((0 : Q') <= fusionModeQ F modeOne k) /\
      (fusionModeQ F modeOne k <= (1 : Q')) := by
  have heq := fusionModeOne_eqv_p2VacNorm F k
  have h0 := p2VacNorm_nonneg (F.N k) (F.hw0 k) (F.hw1 k) 1
  have hret := p2VacNorm_one_le_retuned (F.N k) (F.hw0 k) (F.hw1 k)
  have hret1 : qpow (p2RetunedWeight (F.w k)) (c4 1) <= (1 : Q') :=
    HeatKernelGap.qpow_le_one (p2RetunedWeight_nonneg (F.hw0 k))
      (p2RetunedWeight_le_one (F.hw1 k)) (c4 1)
  exact
    ⟨Q'.le_trans' _ _ _ h0 (Q'.ge_of_eqv heq),
      Q'.le_trans' _ _ _ (Q'.le_of_eqv heq)
        (Q'.le_trans' _ _ _ hret hret1)⟩

/-- The refined reference is in `[0,1]` by the uniform p=2 carrier theorem. -/
theorem refinedModeOne_range (F : P2RetunedControlFamily) (k : Nat) :
    ((0 : Q') <= refinedModeOneQ F k) /\
      (refinedModeOneQ F k <= (1 : Q')) := by
  simpa only [refinedModeOneQ] using
    (corrected_carrier_range (F.hw0 k) (F.hw1 k) 1)

/-- **Physical/reference square-gap bridge.**  This is the all-cutoff
proof-about-computation replacement for evaluating the physical rational
square gap at every scale. -/
theorem modeOne_squareGap_le_refinedGap_add_defects
    (F : P2RetunedControlFamily) (k : Nat) :
    fusionModeQ F modeOne (k + 1) * fusionModeQ F modeOne (k + 1) +
        -(fusionModeQ F modeOne k) <=
      (refinedModeOneQ F (k + 1) * refinedModeOneQ F (k + 1) +
          -(refinedModeOneQ F k)) +
        (Q'.ofNat 2 * modeOneRefinedDefect F (k + 1) +
          modeOneRefinedDefect F k) := by
  have hphys := fusionModeOne_range F (k + 1)
  have href := refinedModeOne_range F (k + 1)
  have herr :
      absQ (fusionModeQ F modeOne (k + 1) +
          -refinedModeOneQ F (k + 1)) <=
        modeOneRefinedDefect F (k + 1) :=
    Q'.le_of_eqv (fusionModeOne_abs_refined_eqv_defect F (k + 1))
  have hcoarse :
      absQ (fusionModeQ F modeOne k + -refinedModeOneQ F k) <=
        modeOneRefinedDefect F k :=
    Q'.le_of_eqv (fusionModeOne_abs_refined_eqv_defect F k)
  exact squareGap_le_referenceSquareGap_add_errors
    hphys.1 hphys.2 href.1 href.2 herr hcoarse

end YMGap.Continuum.P2RetunedFusionReferenceGap

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2RetunedFusionReferenceGap.square_sub_square_eqv
#print axioms YMGap.Continuum.P2RetunedFusionReferenceGap.square_sub_square_le_two_abs
#print axioms YMGap.Continuum.P2RetunedFusionReferenceGap.absQ_sub_comm_eqv
#print axioms YMGap.Continuum.P2RetunedFusionReferenceGap.gap_le_reference_gap_add_errors
#print axioms YMGap.Continuum.P2RetunedFusionReferenceGap.squareGap_le_referenceSquareGap_add_errors
#print axioms YMGap.Continuum.P2RetunedFusionReferenceGap.fusionModeOne_eqv_p2VacNorm
#print axioms YMGap.Continuum.P2RetunedFusionReferenceGap.fusionModeOne_range
#print axioms YMGap.Continuum.P2RetunedFusionReferenceGap.modeOne_squareGap_le_refinedGap_add_defects
