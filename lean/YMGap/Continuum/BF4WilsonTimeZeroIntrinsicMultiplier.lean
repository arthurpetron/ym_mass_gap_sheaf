/-
# Time-zero multiplication on the actual intrinsic Wilson expressions

Multiplication by a source-loop character is placed at the recorded reflection
center and leaves that radius unchanged. Every larger centered chart therefore
places the SAME multiplier on its time-zero slice. The checked original-form
estimate bounds its intrinsic squared norm by characterBound spin.

For distances, both operands are placed at their maximum radius. Polynomial
distributivity identifies the difference of their products with the product
of their difference inside BOTH slots of the actual limiting reflected form.
The same norm estimate then proves the intrinsic distance bound. No ordinary
Haar norm replaces the OS form and no bound is supplied as a new hypothesis.

Literal zero-spatial-shift inclusion commutes with the multiplier. Spatial
union stages, completed operators, and canonical OS/QFT realization are
separate consumers. All existing small-nome guards remain explicit.
-/

import YMGap.Continuum.BF4WilsonTimeZeroMultiplierBound
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion

namespace YMGap.Continuum.BF4WilsonTimeZeroIntrinsicMultiplier

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter (recenterLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion (inclusion)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm
  (distSq distSq_chart toWindow)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
  (chartInsertion chartScalar)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit (spatialLimit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialFunctionalLaws (spatialLimit_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz (form)
open YMGap.Continuum.BF4WilsonTimeZeroMultiplierBound (form_timeZero_multiplier_bound)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (characterBound)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

/-- The original loop is inserted at the expression's reflection center. -/
def multiply {base : Nat} (L : SourceLoop base) (spin : Nat)
    (x : IntrinsicExpression base) : IntrinsicExpression base where
  radius := x.radius
  expression := .mul (.loop x.radius L spin) x.expression
  within := ⟨Nat.le_refl _, x.within⟩

theorem multiply_radius {base : Nat} (L : SourceLoop base) (spin : Nat)
    (x : IntrinsicExpression base) : (multiply L spin x).radius = x.radius := rfl

/-- A common centered chart keeps the multiplier exactly on the common plane. -/
theorem chart_multiply {base : Nat} (H : Nat) (L : SourceLoop base) (spin : Nat)
    (x : IntrinsicExpression base) (hx : x.radius ≤ H) :
    chart H (multiply L spin x) = .mul (.loop H L spin) (chart H x) := by
  change WindowExpression.mul (.loop (x.radius+(H-x.radius)) L spin) (chart H x) = _
  rw [show x.radius+(H-x.radius)=H by omega]

/-- Only the source-box witness changes under zero-spatial-shift inclusion. -/
theorem inclusion_multiply {base larger : Nat} (h : base ≤ larger)
    (L : SourceLoop base) (spin : Nat) (x : IntrinsicExpression base) :
    inclusion h (multiply L spin x) =
      multiply (recenterLoop (space := 0) (by simpa only [Nat.add_zero] using h) L)
        spin (inclusion h x) := rfl

private theorem distribute (a e f : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polyMul a e) (polySmul (-1) (polyMul a f)))
      (polyMul a (polyAdd e (polySmul (-1) f))) :=
  ((RatPolyCoeffEqv.mul_add_right a e (polySmul (-1) f)).trans
    ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.polyMul_smul_right (-1) a f))).symm

attribute [local irreducible] chartScalar spatialLimit

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
  {base : Nat} (hb : 0<base)

private theorem form_distribute_diagonal (H : Nat) (a e f : WindowExpression base)
    (ha : Within H a) (he : Within H e) (hf : Within H f) :
    Equiv (form hw0 hw1 hsmall hd hs hb H
      (.add (.mul a e) (.smul (-1) (.mul a f)))
      (.add (.mul a e) (.smul (-1) (.mul a f)))
      ⟨⟨ha, he⟩, ⟨ha, hf⟩⟩ ⟨⟨ha, he⟩, ⟨ha, hf⟩⟩)
      (form hw0 hw1 hsmall hd hs hb H
        (.mul a (.add e (.smul (-1) f))) (.mul a (.add e (.smul (-1) f)))
        ⟨ha, ⟨he, hf⟩⟩ ⟨ha, ⟨he, hf⟩⟩) := by
  let d : WindowExpression base := .add (.mul a e) (.smul (-1) (.mul a f))
  let m : WindowExpression base := .mul a (.add e (.smul (-1) f))
  have hD : Within H d := ⟨⟨ha, he⟩, ⟨ha, hf⟩⟩
  have hM : Within H m := ⟨ha, ⟨he, hf⟩⟩
  apply spatialLimit_congr hw0 hw1 hsmall hd hs hb H
    (.mul (mirror H d) d) (.mul (mirror H m) m)
    ⟨mirror_within H d, within_mono (by omega : H ≤ 2*H) d hD⟩
    ⟨mirror_within H m, within_mono (by omega : H ≤ 2*H) m hM⟩
  intro r t
  exact (distribute (chartInsertion r H t (mirror H a))
    (chartInsertion r H t (mirror H e)) (chartInsertion r H t (mirror H f))).mul
    (distribute (chartInsertion r H t a) (chartInsertion r H t e) (chartInsertion r H t f))

attribute [local irreducible] form

/-- Squared-norm cap for the SAME intrinsic reflected form, depending only on spin. -/
theorem intrinsicForm_multiplier_bound (L : SourceLoop base) (spin : Nat)
    (x : IntrinsicExpression base) :
    leEv (intrinsicForm hw0 hw1 hsmall hd hs hb (multiply L spin x) (multiply L spin x))
      (mul (ofQ' (characterBound spin)) (intrinsicForm hw0 hw1 hsmall hd hs hb x x)) := by
  have hleft := intrinsicForm_chart hw0 hw1 hsmall hd hs hb
    (multiply L spin x) (multiply L spin x) x.radius (Nat.le_refl _) (Nat.le_refl _)
  have hright := intrinsicForm_chart hw0 hw1 hsmall hd hs hb x x x.radius
    (Nat.le_refl _) (Nat.le_refl _)
  simp only [chart_multiply x.radius L spin x (Nat.le_refl _), chart_self] at hleft
  simp only [chart_self] at hright
  exact leEv_trans (leEv_of_equiv hleft)
    (leEv_trans (form_timeZero_multiplier_bound hw0 hw1 hsmall hd hs hb
      x.radius L spin x.expression x.within)
      (leEv_of_equiv (Pivot2.mul_congr_right hright.symm)))

private theorem window_distSq_multiplier_bound (H : Nat) (L : SourceLoop base) (spin : Nat)
    (e f : WindowExpression base) (he : Within H e) (hf : Within H f) :
    leEv (BF4ExactSlabFixedSpatialWilsonWindowSeminorm.distSq hw0 hw1 hsmall hd hs hb H
      ⟨.mul (.loop H L spin) e, ⟨Nat.le_refl _, he⟩⟩
      ⟨.mul (.loop H L spin) f, ⟨Nat.le_refl _, hf⟩⟩)
      (mul (ofQ' (characterBound spin))
        (BF4ExactSlabFixedSpatialWilsonWindowSeminorm.distSq hw0 hw1 hsmall hd hs hb H
          ⟨e, he⟩ ⟨f, hf⟩)) :=
  leEv_trans (leEv_of_equiv (form_distribute_diagonal hw0 hw1 hsmall hd hs hb H
    (.loop H L spin) e f (Nat.le_refl _) he hf))
    (form_timeZero_multiplier_bound hw0 hw1 hsmall hd hs hb H L spin
      (.add e (.smul (-1) f)) ⟨he, hf⟩)

/-- The actual intrinsic squared distance obeys the same spin-only bound.
Both operands and their products are compared at one explicit common horizon. -/
theorem distSq_multiplier_bound (L : SourceLoop base) (spin : Nat)
    (x y : IntrinsicExpression base) :
    leEv (distSq hw0 hw1 hsmall hd hs hb (multiply L spin x) (multiply L spin y))
      (mul (ofQ' (characterBound spin)) (distSq hw0 hw1 hsmall hd hs hb x y)) := by
  let H := max x.radius y.radius
  have hx : x.radius ≤ H := Nat.le_max_left _ _
  have hy : y.radius ≤ H := Nat.le_max_right _ _
  have hleft := distSq_chart hw0 hw1 hsmall hd hs hb
    (multiply L spin x) (multiply L spin y) H hx hy
  have hright := distSq_chart hw0 hw1 hsmall hd hs hb x y H hx hy
  simp only [toWindow, chart_multiply H L spin x hx, chart_multiply H L spin y hy] at hleft
  exact leEv_trans (leEv_of_equiv hleft)
    (leEv_trans (window_distSq_multiplier_bound hw0 hw1 hsmall hd hs hb H L spin
      (chart H x) (chart H y) (chart_within H x hx) (chart_within H y hy))
      (leEv_of_equiv (Pivot2.mul_congr_right hright.symm)))

#print axioms multiply
#print axioms multiply_radius
#print axioms chart_multiply
#print axioms inclusion_multiply
#print axioms intrinsicForm_multiplier_bound
#print axioms distSq_multiplier_bound

end YMGap.Continuum.BF4WilsonTimeZeroIntrinsicMultiplier
