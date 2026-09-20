/-
# Diagonal translation preserves the ORIGINAL limiting Wilson form

Translate all three spatial coordinates by s and enlarge the source guard
from b to b+2*s. Recentring at margin r then gives literally the same box
and expression as the old margin r+s. This is an exact cofinal identity of
the already constructed time/cutoff limits, not a comparison with a new
action or a claim that unequal finite boxes have identical laws.

The consumer is the original Wilson union's seminorm completion. These
equalities provide its spatial isometries with no new analytic input. They
do not prove independent signed-axis translations, continuum covariance,
changing-spacing control, full observable coverage, or the Clay theorem.
-/

import YMGap.Continuum.BF4WilsonDiagonalTranslationSyntax

namespace YMGap.Continuum.BF4WilsonDiagonalTranslationForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonDiagonalTranslationSyntax
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
  (centeredExpression centered_within)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy (originalJointLimit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter (paddedWidth)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz (form)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm (difference distSq)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

theorem translated_paddedWidth (base s r : Nat) :
    paddedWidth (base+2*s) r = paddedWidth base (r+s) := by
  unfold paddedWidth
  omega

private theorem recenter_heq {base left right first second : Nat}
    (hwidth : left = right) (hshift : first = second)
    (hl : base+first ≤ left) (hr : base+second ≤ right)
    (e : WindowExpression base) :
    HEq (recenterExpression hl e) (recenterExpression hr e) := by
  cases hwidth
  cases hshift
  rfl

/-- HEq records only the proved equality of the dependent finite-box widths. -/
theorem centered_translate {base : Nat} (s r : Nat) (e : WindowExpression base) :
    HEq (centeredExpression r (translateExpression s e))
      (centeredExpression (r+s) e) := by
  have h := recenterExpression_comp (first := s) (second := r+1)
    (middle := base+2*s) (targetWidth := paddedWidth (base+2*s) r)
    (by omega) (by unfold paddedWidth; omega) e
  exact (heq_of_eq h).trans
    (recenter_heq (translated_paddedWidth base s r) (by omega) _ _ e)

private theorem converges_add_shift {f : Nat → CReal} {l : CReal}
    (h : ConvergesTo f l) (s : Nat) : ConvergesTo (fun n => f (n+s)) l := by
  intro epsilon he
  obtain ⟨N, hN⟩ := h epsilon he
  exact ⟨N, fun n hn => hN (n+s) (by omega)⟩

private theorem equiv_of_eq {a b : CReal} (h : a = b) : Equiv a b := by
  cases h
  exact Equiv.refl _

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

private theorem jointLimit_congr_width {left right : Nat} (hwidth : left = right)
    (H : Nat) (e : WindowExpression left) (f : WindowExpression right)
    (he : Within (2*H) e) (hf : Within (2*H) f) (hef : HEq e f) :
    originalJointLimit hw0 hw1 (2*H) e he = originalJointLimit hw0 hw1 (2*H) f hf := by
  cases hwidth
  have heq := eq_of_heq hef
  cases heq
  rfl

/-- SAME full interacting action, original partition, and ordered loop insertion. -/
theorem jointLimit_translate {base : Nat} (s r H : Nat)
    (e : WindowExpression base) (he : Within (2*H) e) :
    originalJointLimit hw0 hw1 (2*H) (centeredExpression r (translateExpression s e))
      ((centered_within r (2*H) _).mpr ((translate_within s (2*H) e).mpr he)) =
    originalJointLimit hw0 hw1 (2*H) (centeredExpression (r+s) e)
      ((centered_within (r+s) (2*H) e).mpr he) :=
  jointLimit_congr_width hw0 hw1 (translated_paddedWidth base s r) H _ _ _ _
    (centered_translate s r e)

variable (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

/-- A cofinal shift of the old convergent sequence, not an assumed invariant limit. -/
theorem spatialLimit_translate {base : Nat} (hb : 0 < base) (s H : Nat)
    (e : WindowExpression base) (he : Within (2*H) e) :
    Equiv (spatialLimit hw0 hw1 H (translateExpression s e)
      ((translate_within s (2*H) e).mpr he) hsmall hd hs (by omega))
      (spatialLimit hw0 hw1 H e he hsmall hd hs hb) := by
  apply Equiv_of_limit_of_equal
    (fun r => equiv_of_eq (jointLimit_translate hw0 hw1 s r H e he))
    (jointLimits_spatial_converge hw0 hw1 H (translateExpression s e)
      ((translate_within s (2*H) e).mpr he) hsmall hd hs (by omega))
    (converges_add_shift (jointLimits_spatial_converge hw0 hw1 H e he hsmall hd hs hb) s)

theorem form_translate {base : Nat} (hb : 0 < base) (s H : Nat)
    (e f : WindowExpression base) (he : Within H e) (hf : Within H f) :
    Equiv (form hw0 hw1 hsmall hd hs (by omega) H
      (translateExpression s e) (translateExpression s f)
      ((translate_within s H e).mpr he) ((translate_within s H f).mpr hf))
      (form hw0 hw1 hsmall hd hs hb H e f he hf) := by
  have h := spatialLimit_translate hw0 hw1 hsmall hd hs hb s H (.mul (mirror H e) f)
    ⟨mirror_within H e, within_mono (by omega : H ≤ 2*H) f hf⟩
  simpa only [form, translateExpression, recenterExpression, mirror, recenter_mapOffsets] using h

/-- Original mixed form on arbitrary radius-tagged Wilson expressions. -/
theorem intrinsicForm_translate {base : Nat} (hb : 0 < base) (s : Nat)
    (x y : IntrinsicExpression base) :
    Equiv (intrinsicForm hw0 hw1 hsmall hd hs (by omega) (translate s x) (translate s y))
      (intrinsicForm hw0 hw1 hsmall hd hs hb x y) := by
  simpa only [intrinsicForm, translate_radius, translate_chart] using
    form_translate hw0 hw1 hsmall hd hs hb s (max x.radius y.radius)
      (chart (max x.radius y.radius) x) (chart (max x.radius y.radius) y)
      (chart_within _ x (Nat.le_max_left _ _)) (chart_within _ y (Nat.le_max_right _ _))

/-- The existing squared distance is preserved; this is the completion-map input. -/
theorem distSq_translate {base : Nat} (hb : 0 < base) (s : Nat)
    (x y : IntrinsicExpression base) :
    Equiv (distSq hw0 hw1 hsmall hd hs (by omega) (translate s x) (translate s y))
      (distSq hw0 hw1 hsmall hd hs hb x y) := by
  simpa only [distSq, translate_difference] using
    intrinsicForm_translate hw0 hw1 hsmall hd hs hb s (difference x y) (difference x y)

#print axioms translated_paddedWidth
#print axioms centered_translate
#print axioms jointLimit_translate
#print axioms spatialLimit_translate
#print axioms form_translate
#print axioms intrinsicForm_translate
#print axioms distSq_translate

end YMGap.Continuum.BF4WilsonDiagonalTranslationForm
