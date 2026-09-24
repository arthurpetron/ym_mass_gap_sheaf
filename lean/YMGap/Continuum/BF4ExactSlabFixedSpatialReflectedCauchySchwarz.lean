/-
# Sharp Cauchy--Schwarz for the actual reflected window limit

At each finite symmetric placement, the original selected-chain reflected
positivity theorem applies to every signed combination of physical probe
spans. Its exact quadratic expansion constructs a rational PreInnerForm,
so the existing sharp rational Cauchy--Schwarz theorem applies to the SAME
finite window ratios and partition.

The three raw time sequences then converge to the already constructed mixed
window form. General multiplication continuity passes the inequality to
those limits without identifying their different polynomial caps or QMhat
indices. The limiting radical pairs to zero by an epsilon-squared estimate.

Nome, width and retained heat cutoff are fixed. No physical transfer,
completed OS quotient, cutoff removal or continuum mass gap is supplied.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm
import YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedSymmetry
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedCauchySchwarz

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedSymmetry
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.OSReconstructionProgress

local infix:50 " ≈ " => Q'.eqv

def finitePairing {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width h stage t : Nat) (xs ys : Span) : Q' :=
  windowRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
    t (2*h) t (mixedProduct width h xs ys)

theorem finite_add_left {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width h stage t : Nat) (xs ys zs : Span) :
    finitePairing hw0 hw1 width h stage t (xs++ys) zs ≈
      finitePairing hw0 hw1 width h stage t xs zs +
        finitePairing hw0 hw1 width h stage t ys zs := by
  unfold finitePairing
  rw [mixedProduct_add_left]
  exact windowRatio_add hw0 hw1 _ width _ t (2*h) t _ _

theorem finite_add_right {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width h stage t : Nat) (xs ys zs : Span) :
    finitePairing hw0 hw1 width h stage t xs (ys++zs) ≈
      finitePairing hw0 hw1 width h stage t xs ys +
        finitePairing hw0 hw1 width h stage t xs zs :=
  Q'.eqv_trans _ _ _
    (windowRatio_congr hw0 hw1 _ width _ t (2*h) t
      (mixedProduct_add_right width h xs ys zs))
    (windowRatio_add hw0 hw1 _ width _ t (2*h) t _ _)

theorem finite_smul_left {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width h stage t : Nat) (c : Q') (xs ys : Span) :
    finitePairing hw0 hw1 width h stage t (scaleSpan c xs) ys ≈
      c * finitePairing hw0 hw1 width h stage t xs ys :=
  Q'.eqv_trans _ _ _
    (windowRatio_congr hw0 hw1 _ width _ t (2*h) t
      (mixedProduct_smul_left width h c xs ys))
    (windowRatio_smul hw0 hw1 _ width _ t (2*h) t c _)

theorem finite_smul_right {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width h stage t : Nat) (c : Q') (xs ys : Span) :
    finitePairing hw0 hw1 width h stage t xs (scaleSpan c ys) ≈
      c * finitePairing hw0 hw1 width h stage t xs ys :=
  Q'.eqv_trans _ _ _
    (windowRatio_congr hw0 hw1 _ width _ t (2*h) t
      (mixedProduct_smul_right width h c xs ys))
    (windowRatio_smul hw0 hw1 _ width _ t (2*h) t c _)

theorem finite_symm {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width h stage t : Nat) (xs ys : Span)
    (hx : Within h xs) (hy : Within h ys)
    (hxf : Physical width xs) (hyf : Physical width ys) :
    finitePairing hw0 hw1 width h stage t xs ys ≈
      finitePairing hw0 hw1 width h stage t ys xs :=
  reflectedWindowRatio_symm hw0 hw1 width h xs ys hx hxf hy hyf stage t

/-- The physical domain is retained by the actual signed combination. -/
def guardedSpan (width h : Nat) :=
  {xs : Span // Within h xs ∧ Physical width xs}

def finitePreInnerForm {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width h stage t : Nat) : PreInnerForm (guardedSpan width h) where
  B := fun xs ys => finitePairing hw0 hw1 width h stage t xs.val ys.val
  nonnegQuad := by
    intro s r x y
    let xs := x.val
    let ys := y.val
    let combination := scaleSpan s xs ++ scaleSpan r ys
    let F := finitePairing hw0 hw1 width h stage t
    have hx : Within h xs := x.property.1
    have hy : Within h ys := y.property.1
    have hxf : Physical width xs := x.property.2
    have hyf : Physical width ys := y.property.2
    have hleft : F xs combination ≈ s * F xs xs + r * F xs ys :=
      Q'.eqv_trans _ _ _
        (finite_add_right hw0 hw1 width h stage t xs (scaleSpan s xs) (scaleSpan r ys))
        (Q'.add_eqv_congr'
          (finite_smul_right hw0 hw1 width h stage t s xs xs)
          (finite_smul_right hw0 hw1 width h stage t r xs ys))
    have hright : F ys combination ≈ s * F xs ys + r * F ys ys :=
      Q'.eqv_trans _ _ _
        (finite_add_right hw0 hw1 width h stage t ys (scaleSpan s xs) (scaleSpan r ys))
        (Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _
            (finite_smul_right hw0 hw1 width h stage t s ys xs)
            (Q'.mul_eqv_congr_left _ _ _ (finite_symm hw0 hw1 width h stage t ys xs hy hx hyf hxf)))
          (finite_smul_right hw0 hw1 width h stage t r ys ys))
    have hscaledLeft : F (scaleSpan s xs) combination ≈
        s * (s * F xs xs + r * F xs ys) :=
      Q'.eqv_trans _ _ _ (finite_smul_left hw0 hw1 width h stage t s xs combination)
        (Q'.mul_eqv_congr_left _ _ _ hleft)
    have hscaledRight : F (scaleSpan r ys) combination ≈
        r * (s * F xs ys + r * F ys ys) :=
      Q'.eqv_trans _ _ _ (finite_smul_left hw0 hw1 width h stage t r ys combination)
        (Q'.mul_eqv_congr_left _ _ _ hright)
    have hexpand : F combination combination ≈
        s * (s * F xs xs + r * F xs ys) + r * (s * F xs ys + r * F ys ys) :=
      Q'.eqv_trans _ _ _
        (finite_add_left hw0 hw1 width h stage t (scaleSpan s xs) (scaleSpan r ys) combination)
        (Q'.add_eqv_congr' hscaledLeft hscaledRight)
    have hquad : F combination combination ≈
        s*s*F xs xs + 2*(s*r)*F xs ys + r*r*F ys ys :=
      Q'.eqv_trans _ _ _ hexpand (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_add_eqv s (s*F xs xs) (r*F xs ys))
          (Q'.mul_add_eqv r (s*F xs ys) (r*F ys ys)))
        (YMGap.Continuum.GNSQuotient.GNSData.quad_regroup s r (F xs xs) (F xs ys) (F ys ys)))
    have hnonnegative : (0 : Q') ≤ F combination combination :=
      reflectedWindowRatio_nonnegative hw0 hw1 width h combination
        (within_append (within_scale s hx) (within_scale r hy))
        (physical_append (physical_scale s hxf) (physical_scale r hyf)) stage t
    exact Q'.le_trans' _ _ _ hnonnegative (Q'.le_of_eqv hquad)

/-- Sharp CS for the actual finite reflected ratios, all sharing one partition. -/
theorem finite_cauchySchwarz {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width h : Nat) (xs ys : Span) (hx : Within h xs) (hy : Within h ys)
    (hxf : Physical width xs) (hyf : Physical width ys) (stage t : Nat) :
    windowRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        t (2*h) t (mixedProduct width h xs ys) *
      windowRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        t (2*h) t (mixedProduct width h xs ys) ≤
      windowRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        t (2*h) t (mixedProduct width h xs xs) *
      windowRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        t (2*h) t (mixedProduct width h ys ys) :=
  (finitePreInnerForm hw0 hw1 width h stage t).cauchy_schwarz
    ⟨xs, hx, hxf⟩ ⟨ys, hy, hyf⟩

/-- Sharp CS passes through the three raw time sequences, not matched CReal
approximation indices. No additional uniform bound is an input. -/
theorem form_cauchySchwarz {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width h : Nat) (xs ys : Span) (hx : Within h xs) (hy : Within h ys)
    (hxf : Physical width xs) (hyf : Physical width ys) (stage : Nat) :
    leEv (mul (form hw0 hw1 width h xs ys hx hy stage)
        (form hw0 hw1 width h xs ys hx hy stage))
      (mul (form hw0 hw1 width h xs xs hx hx stage)
        (form hw0 hw1 width h ys ys hy hy stage)) := by
  have hxy := form_converges hw0 hw1 width h xs ys hx hy stage
  have hxx := form_converges hw0 hw1 width h xs xs hx hx stage
  have hyy := form_converges hw0 hw1 width h ys ys hy hy stage
  refine leEv_of_convergesTo_le
    (YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general hxy hxy)
    (YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general hxx hyy) ?_
  intro t epsilon hepsilon
  refine ⟨0, fun n _ => ?_⟩
  change finitePairing hw0 hw1 width h stage t xs ys *
      finitePairing hw0 hw1 width h stage t xs ys ≤
    finitePairing hw0 hw1 width h stage t xs xs *
      finitePairing hw0 hw1 width h stage t ys ys + epsilon
  exact Q'.le_trans' _ _ _
    (finite_cauchySchwarz hw0 hw1 width h xs ys hx hy hxf hyf stage t)
    (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon))

private theorem zero_of_square_le_zero (A : CReal)
    (h : leEv (mul A A) (ofQ' 0)) : Equiv A (ofQ' 0) := by
  intro epsilon he
  obtain ⟨index, hN⟩ := h (epsilon*epsilon) (Q'.mul_pos he he)
  refine ⟨index, fun n hn => ?_⟩
  have hs : A.approx n * A.approx n ≤ epsilon*epsilon := by
    have hs := hN n hn
    change A.approx n * A.approx n ≤ 0 + epsilon*epsilon at hs
    rwa [Q'.zero_add'] at hs
  have ha := Q'.abs_le_two_sided (Q'.abs_le_of_sq_le_sq he hs)
  constructor
  · exact Q'.le_trans' _ _ _ ha.1 (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' _)))
  · apply Q'.le_add_of_sub_le
    change 0 + -A.approx n ≤ epsilon
    rw [Q'.zero_add']
    exact ha.2

/-- Null vectors of this SAME reflected form pair to zero. The proof uses
epsilon squared and no square root, division or positivity decision. -/
theorem form_radical_zero {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width h : Nat) (xs ys : Span) (hx : Within h xs) (hy : Within h ys)
    (hxf : Physical width xs) (hyf : Physical width ys) (stage : Nat)
    (hnull : Equiv (form hw0 hw1 width h xs xs hx hx stage) (ofQ' 0)) :
    Equiv (form hw0 hw1 width h xs ys hx hy stage) (ofQ' 0) :=
  zero_of_square_le_zero _ (leEv_trans
    (form_cauchySchwarz hw0 hw1 width h xs ys hx hy hxf hyf stage)
    (leEv_of_equiv ((YMGap.Continuum.Pivot2.mul_congr_left hnull).trans
      (SumOfSquares.Equiv_of_approx_eqv (fun n =>
        Q'.zero_mul_eqv ((form hw0 hw1 width h ys ys hy hy stage).approx n))))))

end YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedCauchySchwarz

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedCauchySchwarz.finite_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedCauchySchwarz.form_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedCauchySchwarz.form_radical_zero
