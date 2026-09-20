/-
# Diagonal spatial translation of original Wilson syntax

This module records only the literal spatial recentering of an intrinsic
Wilson expression.  It preserves the radius tag, time offsets, and finite
algebraic syntax.  No action, form, limit, or translation estimate is added.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion

namespace YMGap.Continuum.BF4WilsonDiagonalTranslationSyntax

set_option autoImplicit false

open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion

def translateExpression {base : Nat} (s : Nat) (e : WindowExpression base) :
    WindowExpression (base + 2*s) :=
  recenterExpression (space := s) (by omega : base+s ≤ base+2*s) e

def translate {base : Nat} (s : Nat) (x : IntrinsicExpression base) :
    IntrinsicExpression (base + 2*s) where
  radius := x.radius
  expression := translateExpression s x.expression
  within := (recenter_within (by omega : base+s ≤ base+2*s) x.radius x.expression).mpr x.within

theorem translate_within {base : Nat} (s L : Nat) (e : WindowExpression base)
    : Within L (translateExpression s e) ↔ Within L e :=
  recenter_within (by omega : base+s ≤ base+2*s) L e

theorem translate_radius {base : Nat} (s : Nat) (x : IntrinsicExpression base) :
    (translate s x).radius = x.radius := rfl

theorem translate_chart {base : Nat} (s H : Nat) (x : IntrinsicExpression base) :
    chart H (translate s x) = translateExpression s (chart H x) := by
  exact (recenter_mapOffsets (by omega : base+s ≤ base+2*s)
    (fun offset => offset + (H-x.radius)) x.expression).symm

theorem translate_advance {base : Nat} (s n : Nat) (x : IntrinsicExpression base) :
    translate s (advance n x) = advance n (translate s x) := rfl

theorem translate_unit (base s : Nat) :
    translate s (unit base) = unit (base + 2*s) := rfl

theorem translateExpression_inclusion {base larger : Nat} (h : base ≤ larger) (s : Nat)
    (e : WindowExpression base) :
    includeExpression (Nat.add_le_add_right h (2*s)) (translateExpression s e) =
      translateExpression s (includeExpression h e) := by
  unfold includeExpression translateExpression
  have hl := recenterExpression_comp
    (width := base) (middle := base+2*s) (targetWidth := larger+2*s)
    (first := s) (second := 0)
    (by omega : base+s ≤ base+2*s)
    (by omega : (base+2*s)+0 ≤ larger+2*s) e
  have hr := recenterExpression_comp
    (width := base) (middle := larger) (targetWidth := larger+2*s)
    (first := 0) (second := s)
    (by omega : base+0 ≤ larger)
    (by omega : larger+s ≤ larger+2*s) e
  simp only [Nat.add_zero, Nat.zero_add] at hl hr
  exact hl.trans hr.symm

private theorem intrinsic_ext {base : Nat} (x y : IntrinsicExpression base)
    (hr : x.radius = y.radius) (he : x.expression = y.expression) : x = y := by
  cases x
  cases y
  cases hr
  cases he
  rfl

theorem translate_difference {base : Nat} (s : Nat)
    (x y : IntrinsicExpression base) :
    translate s (difference x y) = difference (translate s x) (translate s y) := by
  apply intrinsic_ext
  · rfl
  · change translateExpression s
      (.add (chart (max x.radius y.radius) x)
        (.smul (-1) (chart (max x.radius y.radius) y))) =
      .add (chart (max x.radius y.radius) (translate s x))
        (.smul (-1) (chart (max x.radius y.radius) (translate s y)))
    simp only [translateExpression, recenterExpression]
    rw [translate_chart, translate_chart]
    rfl

theorem translate_inclusion {base larger : Nat} (h : base ≤ larger) (s : Nat)
    (x : IntrinsicExpression base) :
    inclusion (Nat.add_le_add_right h (2*s)) (translate s x) =
      translate s (inclusion h x) := by
  apply intrinsic_ext
  · rfl
  · exact translateExpression_inclusion h s x.expression

private theorem intrinsic_heq {left right : Nat} (hb : left = right)
    (x : IntrinsicExpression left) (y : IntrinsicExpression right)
    (hr : x.radius = y.radius) (he : HEq x.expression y.expression) : HEq x y := by
  cases hb
  exact heq_of_eq (intrinsic_ext x y hr (eq_of_heq he))

private theorem recenter_heq {base left right first second : Nat}
    (hb : left = right) (hs : first = second)
    (hl : base+first ≤ left) (hr : base+second ≤ right)
    (e : WindowExpression base) :
    HEq (recenterExpression hl e) (recenterExpression hr e) := by
  cases hb
  cases hs
  rfl

theorem translate_zero {base : Nat} (x : IntrinsicExpression base) :
    HEq (translate 0 x) x := by
  apply intrinsic_heq (by omega) (translate 0 x) x rfl
  simpa only [translate, translateExpression, includeExpression, Nat.mul_zero, Nat.add_zero] using
    heq_of_eq (includeExpression_refl x.expression)

/-- Only the support types differ; their base arithmetic is proved explicitly. -/
theorem translate_add {base : Nat} (m n : Nat) (x : IntrinsicExpression base) :
    HEq (translate (m+n) x) (translate m (translate n x)) := by
  apply intrinsic_heq (by omega) (translate (m+n) x) (translate m (translate n x)) rfl
  have h := recenterExpression_comp (first := n) (second := m)
    (middle := base+2*n) (targetWidth := (base+2*n)+2*m)
    (by omega) (by omega) x.expression
  exact (recenter_heq (by omega) (by omega) _ _ x.expression).trans (heq_of_eq h.symm)

#print axioms translateExpression
#print axioms translate
#print axioms translate_within
#print axioms translate_radius
#print axioms translate_chart
#print axioms translate_advance
#print axioms translate_unit
#print axioms translateExpression_inclusion
#print axioms translate_difference
#print axioms translate_inclusion
#print axioms translate_zero
#print axioms translate_add

end YMGap.Continuum.BF4WilsonDiagonalTranslationSyntax
