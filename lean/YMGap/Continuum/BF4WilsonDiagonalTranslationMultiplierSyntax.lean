/-
# Diagonal translation of original Wilson multipliers

The existing spatial recentering transports a literal source loop together
with an intrinsic Wilson expression.  This is only syntax and dependent-base
interoperability; no new norm or action estimate is introduced.
-/

import YMGap.Continuum.BF4WilsonDiagonalTranslationSyntax
import YMGap.Continuum.BF4WilsonSpatialUnionDiagonalTranslation
import YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroMultiplier

namespace YMGap.Continuum.BF4WilsonDiagonalTranslationMultiplierSyntax

set_option autoImplicit false

open YMGap.Continuum.BF4WilsonDiagonalTranslationSyntax
open YMGap.Continuum.BF4WilsonSpatialUnionDiagonalTranslation
open YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroMultiplier
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4WilsonTimeZeroIntrinsicMultiplier
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion (inclusion_refl)

def translatedLoop {base : Nat} (s : Nat) (L : SourceLoop base) :
    SourceLoop (base + 2*s) :=
  recenterLoop (space := s) (by omega : base+s ≤ base+2*s) L

private theorem translatedLoop_loopAt {base larger : Nat} (s : Nat)
    (L : SourceLoop base) (h : base ≤ larger) :
    translatedLoop s (loopAt L h) =
      loopAt (translatedLoop s L) (Nat.add_le_add_right h (2*s)) := by
  unfold translatedLoop loopAt
  have hl := recenterLoop_comp
    (width := base) (middle := larger) (targetWidth := larger+2*s)
    (first := 0) (second := s)
    (by omega : base+0 ≤ larger)
    (by omega : larger+s ≤ larger+2*s) L
  have hr := recenterLoop_comp
    (width := base) (middle := base+2*s) (targetWidth := larger+2*s)
    (first := s) (second := 0)
    (by omega : base+s ≤ base+2*s)
    (by omega : (base+2*s)+0 ≤ larger+2*s) L
  simp only [Nat.add_zero, Nat.zero_add] at hl hr
  exact hl.trans hr.symm

theorem translate_multiply {base : Nat} (s : Nat) (L : SourceLoop base)
    (spin : Nat) (x : IntrinsicExpression base) :
    translate s (multiply L spin x) =
      multiply (translatedLoop s L) spin (translate s x) := by
  rfl

private theorem max_add_shift (left right shift : Nat) :
    max (left + shift) (right + shift) = max left right + shift := by
  omega

private theorem stage_eq_of_same_base {x y : Stage} (hb : x.base = y.base)
    (hv : atBase x (Nat.le_refl _) =
      atBase y (Nat.le_of_eq hb.symm)) : x = y := by
  cases x
  cases y
  cases hb
  simp only [atBase, inclusion_refl] at hv
  cases hv
  rfl

theorem stageTranslate_multiplyStage {base : Nat} (s : Nat) (L : SourceLoop base)
    (spin : Nat) (x : Stage) :
    stageTranslate s (multiplyStage L spin x) =
      multiplyStage (translatedLoop s L) spin (stageTranslate s x) := by
  let N := max base x.base
  have hL : base ≤ N := Nat.le_max_left _ _
  have hx : x.base ≤ N := Nat.le_max_right _ _
  have hbase : max base x.base + 2*s = max (base+2*s) (x.base+2*s) :=
    (max_add_shift base x.base (2*s)).symm
  apply stage_eq_of_same_base hbase
  change atBase (stageTranslate s (multiplyStage L spin x)) (Nat.le_refl (N+2*s)) =
    atBase (multiplyStage (translatedLoop s L) spin (stageTranslate s x))
      (Nat.max_le.mpr ⟨Nat.add_le_add_right hL (2*s), Nat.add_le_add_right hx (2*s)⟩)
  rw [stageTranslate_atBase s (multiplyStage L spin x) (larger := N) (Nat.le_refl N)]
  rw [atBase_multiply L spin x hL hx]
  rw [translate_multiply]
  rw [translatedLoop_loopAt]
  rw [atBase_multiply (translatedLoop s L) spin (stageTranslate s x)
    (Nat.add_le_add_right hL (2*s)) (Nat.add_le_add_right hx (2*s))]
  rw [stageTranslate_atBase s x hx]

#print axioms translatedLoop
#print axioms translatedLoop_loopAt
#print axioms translate_multiply
#print axioms stageTranslate_multiplyStage

end YMGap.Continuum.BF4WilsonDiagonalTranslationMultiplierSyntax
