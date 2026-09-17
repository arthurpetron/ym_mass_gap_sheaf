/-
# Intrinsic finite-horizon Wilson expressions and their actual reflected form

An expression carries a finite lower-window radius and its explicit support
proof. Inclusion into a larger half-window moves all offsets by the radius
difference, so distances from the reflection plane are retained. Both mixed
factors share one source-coordinate lift under further inclusion.

The intrinsic form is the already constructed original spatial Wilson form
at the maximum of the two recorded radii. Its common-chart theorem follows
from the proved centered-window limit identity, including the simultaneous
movement of both observables and the reflection plane. It does not change
the action, choose a new limit or assume window independence.

These same-base, fixed-spacing, small-nome SU(2) data do not yet construct a
quotient/completion, full gauge-observable coverage, strict bound on this
enlarged carrier, or a continuum quantum field theory.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredLimit
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedFormLaws
import YMGap.Continuum.BoundedRationalCauchyProduct

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit (spatialCauchy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz (form)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedFormLaws
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages

/-- The radius is witnessed data, not a minimality assertion or an erased
existential. The expression retains every actual loop, spin and signed term. -/
structure IntrinsicExpression (base : Nat) where
  radius : Nat
  expression : WindowExpression base
  within : Within radius expression

/-- Center inclusion preserves distance from the plane. Semantic uses carry
the radius bound that excludes truncated-subtraction aliasing. -/
def chart {base : Nat} (H : Nat) (x : IntrinsicExpression base) : WindowExpression base :=
  shift (H-x.radius) x.expression

theorem chart_within {base : Nat} (H : Nat) (x : IntrinsicExpression base)
    (hx : x.radius ≤ H) : Within H (chart H x) := by
  have h := shift_within x.radius (H-x.radius) x.expression x.within
  have hr : x.radius+(H-x.radius)=H := by omega
  simpa only [chart, hr] using h

theorem chart_self {base : Nat} (x : IntrinsicExpression base) :
    chart x.radius x = x.expression := by
  simp only [chart, Nat.sub_self, shift_zero]

/-- Inclusion through an intermediate valid center is exact on the syntax. -/
theorem chart_step {base : Nat} (H d : Nat) (x : IntrinsicExpression base)
    (hx : x.radius ≤ H) : chart (H+d) x = shift d (chart H x) := by
  have ht : H+d-x.radius=(H-x.radius)+d := by omega
  simp only [chart, shift_comp, ht]

/-- The entire source expression, not individual factors, has one common lift. -/
theorem chart_source_step {base : Nat} (blocks H d : Nat) (x : IntrinsicExpression base)
    (hx : x.radius ≤ H) :
    PaddedPolynomialCoeffEqv blocks (sourcePolynomial (chart (H+d) x))
      (liftBoundary (d*(baseLinks base).length) (sourcePolynomial (chart H x))) := by
  rw [chart_step H d x hx]
  exact source_shift blocks d (chart H x)

/-- The complete mixed reflected source retains the SAME coordinate lift. -/
theorem chart_mixed_source_step {base : Nat} (blocks H d : Nat)
    (x y : IntrinsicExpression base) (hx : x.radius ≤ H) (hy : y.radius ≤ H) :
    PaddedPolynomialCoeffEqv blocks
      (sourcePolynomial (.mul (mirror (H+d) (chart (H+d) x)) (chart (H+d) y)))
      (liftBoundary (d*(baseLinks base).length)
        (sourcePolynomial (.mul (mirror H (chart H x)) (chart H y)))) := by
  rw [chart_step H d x hx, chart_step H d y hy]
  exact mixed_source_shift blocks H d (chart H x) (chart H y) (chart_within H x hx)

def unit (base : Nat) : IntrinsicExpression base := ⟨0, .one, True.intro⟩

theorem chart_unit (base H : Nat) : chart H (unit base) = .one := rfl

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
  {base : Nat} (hb : 0<base)

/-- The existing original limiting form at the computed common radius. -/
def intrinsicForm (x y : IntrinsicExpression base) : CReal :=
  form hw0 hw1 hsmall hd hs hb (max x.radius y.radius)
    (chart (max x.radius y.radius) x) (chart (max x.radius y.radius) y)
    (chart_within _ x (Nat.le_max_left _ _)) (chart_within _ y (Nat.le_max_right _ _))

/-- Explicit modulus for the SAME chosen real representative; it is not
extracted from equivalence with another chart or from a proposition. -/
def intrinsicFormCauchy (x y : IntrinsicExpression base) :
    QCauchy (intrinsicForm hw0 hw1 hsmall hd hs hb x y).approx :=
  let H := max x.radius y.radius
  BoundedRationalCauchyProduct.representativeCauchy _
    (spatialCauchy hw0 hw1 H (.mul (mirror H (chart H x)) (chart H y))
      ⟨mirror_within H (chart H x), within_mono (by omega : H ≤ 2*H) _
        (chart_within H y (Nat.le_max_right _ _))⟩ hsmall hd hs hb)

private theorem form_centered_shift (H d : Nat) (e f : WindowExpression base)
    (he : Within H e) (hf : Within H f) :
    Equiv (form hw0 hw1 hsmall hd hs hb (H+d) (shift d e) (shift d f)
      (shift_within H d e he) (shift_within H d f hf))
      (form hw0 hw1 hsmall hd hs hb H e f he hf) :=
  spatialReflected_centered_shift hw0 hw1 hsmall hd hs hb H d e f he hf

attribute [local irreducible] form

/-- Every valid common center realizes the SAME intrinsic mixed value.
The comparison shifts both operands together, never the center alone. -/
theorem intrinsicForm_chart (x y : IntrinsicExpression base) (H : Nat)
    (hx : x.radius ≤ H) (hy : y.radius ≤ H) :
    Equiv (intrinsicForm hw0 hw1 hsmall hd hs hb x y)
      (form hw0 hw1 hsmall hd hs hb H (chart H x) (chart H y)
        (chart_within H x hx) (chart_within H y hy)) := by
  let M := max x.radius y.radius
  have hxM : x.radius ≤ M := Nat.le_max_left _ _
  have hyM : y.radius ≤ M := Nat.le_max_right _ _
  have hMH : M ≤ H := Nat.max_le.mpr ⟨hx, hy⟩
  have hsum : M+(H-M)=H := by omega
  have hcx : shift (H-M) (chart M x) = chart H x := by
    rw [← chart_step M (H-M) x hxM, hsum]
  have hcy : shift (H-M) (chart M y) = chart H y := by
    rw [← chart_step M (H-M) y hyM, hsum]
  have h := form_centered_shift hw0 hw1 hsmall hd hs hb M (H-M)
    (chart M x) (chart M y) (chart_within M x hxM) (chart_within M y hyM)
  simpa only [hsum, hcx, hcy, intrinsicForm, M] using h.symm

theorem intrinsicForm_symm (x y : IntrinsicExpression base) :
    Equiv (intrinsicForm hw0 hw1 hsmall hd hs hb x y)
      (intrinsicForm hw0 hw1 hsmall hd hs hb y x) :=
  (form_symm hw0 hw1 hsmall hd hs hb (max x.radius y.radius)
    (chart (max x.radius y.radius) x) (chart (max x.radius y.radius) y)
    (chart_within _ x (Nat.le_max_left _ _)) (chart_within _ y (Nat.le_max_right _ _))).trans
    (intrinsicForm_chart hw0 hw1 hsmall hd hs hb y x (max x.radius y.radius)
      (Nat.le_max_right _ _) (Nat.le_max_left _ _)).symm

theorem intrinsicForm_nonnegative (x : IntrinsicExpression base) :
    leEv (ofQ' 0) (intrinsicForm hw0 hw1 hsmall hd hs hb x x) :=
  form_nonnegative hw0 hw1 hsmall hd hs hb (max x.radius x.radius)
    (chart (max x.radius x.radius) x) (chart_within _ x (Nat.le_max_left _ _))

theorem intrinsicForm_unit_unit :
    Equiv (intrinsicForm hw0 hw1 hsmall hd hs hb (unit base) (unit base)) (ofQ' 1) := by
  simpa only [intrinsicForm, unit, chart, Nat.max_self, Nat.sub_self, shift_zero] using
    (form_one_one hw0 hw1 hsmall hd hs hb 0)

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm.chart
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm.chart_within
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm.chart_self
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm.chart_step
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm.chart_source_step
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm.chart_mixed_source_step
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm.unit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm.chart_unit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm.intrinsicForm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm.intrinsicFormCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm.intrinsicForm_chart
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm.intrinsicForm_symm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm.intrinsicForm_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm.intrinsicForm_unit_unit
