/-
# Ordinary Cauchy--Schwarz on one original Wilson chart

The finite bilinear form is the ordinary original expectation of a product,
with one selected action and reciprocal partition. Its positivity comes from
the existing full-window square certificate. This is not the reflected OS
form, and the spatial-limit passage is deliberately left to its consumer.
-/

import YMGap.Continuum.BF4WilsonSignedTimeExpectation

namespace YMGap.Continuum.BF4WilsonSignedTimeFiniteCauchySchwarz

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialFunctionalLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit (originalWindowScalar_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws (windowRatio_square_nonnegative)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.OSReconstructionProgress

local infix:50 " ≈ " => Q'.eqv

/-- A supported ordinary square is nonnegative under the original selected
finite action, including its unchanged reciprocal partition. -/
theorem chart_square_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (H : Nat) (e : WindowExpression base) (he : Within (2*H) e)
    (r stage t : Nat) :
    (0 : Q') ≤ chartScalar hw0 hw1 H (.mul e e) r stage t := by
  have hp := chartScalar_original_pin hw0 hw1 H (.mul e e) ⟨he, he⟩ r stage t
  have hc := (centered_within r (2*H) (.mul e e)).mpr ⟨he, he⟩
  have hq := originalWindowScalar_pin hw0 hw1 (2*H)
    (centeredExpression r (.mul e e)) hc stage t t
  have hsupport := source_supported (2*H) (centeredExpression r e)
    ((centered_within r (2*H) e).mpr he)
  have hfinite := windowRatio_square_nonnegative hw0 hw1 (headCutoff w+stage)
    (BF4ExactSlabFixedSpatialSpatialRecenter.paddedWidth base r)
    (Nat.le_add_right _ _) t (2*H) t hsupport
  exact Q'.le_trans' _ _ _ hfinite
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hq) (Q'.ge_of_eqv hp))

private def finitePairing {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (H r stage t : Nat) (e f : WindowExpression base) : Q' :=
  chartScalar hw0 hw1 H (.mul e f) r stage t

private theorem finite_symm {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (H r stage t : Nat) (e f : WindowExpression base) :
    finitePairing hw0 hw1 H r stage t e f ≈
      finitePairing hw0 hw1 H r stage t f e :=
  chartScalar_congr hw0 hw1 H _ _ r stage t (RatPolyCoeffEqv.mul_comm _ _)

private theorem finite_add_left {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (H r stage t : Nat) (e f g : WindowExpression base) :
    finitePairing hw0 hw1 H r stage t (.add e f) g ≈
      finitePairing hw0 hw1 H r stage t e g + finitePairing hw0 hw1 H r stage t f g := by
  have hp : RatPolyCoeffEqv
      (chartInsertion r H t (.mul (.add e f) g))
      (chartInsertion r H t (.add (.mul e g) (.mul f g))) := by
    change RatPolyCoeffEqv
      (polyMul (polyAdd (chartInsertion r H t e) (chartInsertion r H t f))
        (chartInsertion r H t g)) _
    rw [polyMul_add_left_exact]
    exact RatPolyCoeffEqv.refl _
  exact Q'.eqv_trans _ _ _ (chartScalar_congr hw0 hw1 H _ _ r stage t hp)
    (chartScalar_add hw0 hw1 H _ _ r stage t)

private theorem finite_add_right {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (H r stage t : Nat) (e f g : WindowExpression base) :
    finitePairing hw0 hw1 H r stage t e (.add f g) ≈
      finitePairing hw0 hw1 H r stage t e f + finitePairing hw0 hw1 H r stage t e g := by
  have hp : RatPolyCoeffEqv
      (chartInsertion r H t (.mul e (.add f g)))
      (chartInsertion r H t (.add (.mul e f) (.mul e g))) :=
    RatPolyCoeffEqv.mul_add_right _ _ _
  exact Q'.eqv_trans _ _ _ (chartScalar_congr hw0 hw1 H _ _ r stage t hp)
    (chartScalar_add hw0 hw1 H _ _ r stage t)

private theorem finite_smul_left {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (H r stage t : Nat) (c : Q') (e f : WindowExpression base) :
    finitePairing hw0 hw1 H r stage t (.smul c e) f ≈
      c * finitePairing hw0 hw1 H r stage t e f := by
  have hp : RatPolyCoeffEqv
      (chartInsertion r H t (.mul (.smul c e) f))
      (chartInsertion r H t (.smul c (.mul e f))) :=
    RatPolyCoeffEqv.polyMul_smul_left c _ _
  exact Q'.eqv_trans _ _ _ (chartScalar_congr hw0 hw1 H _ _ r stage t hp)
    (chartScalar_smul hw0 hw1 H c _ r stage t)

private theorem finite_smul_right {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (H r stage t : Nat) (c : Q') (e f : WindowExpression base) :
    finitePairing hw0 hw1 H r stage t e (.smul c f) ≈
      c * finitePairing hw0 hw1 H r stage t e f := by
  have hp : RatPolyCoeffEqv
      (chartInsertion r H t (.mul e (.smul c f)))
      (chartInsertion r H t (.smul c (.mul e f))) :=
    RatPolyCoeffEqv.polyMul_smul_right c _ _
  exact Q'.eqv_trans _ _ _ (chartScalar_congr hw0 hw1 H _ _ r stage t hp)
    (chartScalar_smul hw0 hw1 H c _ r stage t)

private def guardedExpression (base H : Nat) :=
  {e : WindowExpression base // Within (2*H) e}

/-- Positivity of every rational linear combination under the same finite
original action provides the constructive sharp rational inequality. -/
private def finitePreInnerForm {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base H r stage t : Nat) : PreInnerForm (guardedExpression base H) where
  B := fun e f => finitePairing hw0 hw1 H r stage t e.val f.val
  nonnegQuad := by
    intro s u x y
    let e := x.val
    let f := y.val
    let combination : WindowExpression base := .add (.smul s e) (.smul u f)
    let F : WindowExpression base → WindowExpression base → Q' :=
      finitePairing hw0 hw1 H r stage t
    have he : Within (2*H) e := x.property
    have hf : Within (2*H) f := y.property
    have hleft : F e combination ≈ s * F e e + u * F e f :=
      Q'.eqv_trans _ _ _
        (finite_add_right hw0 hw1 H r stage t e (.smul s e) (.smul u f))
        (Q'.add_eqv_congr'
          (finite_smul_right hw0 hw1 H r stage t s e e)
          (finite_smul_right hw0 hw1 H r stage t u e f))
    have hright : F f combination ≈ s * F e f + u * F f f :=
      Q'.eqv_trans _ _ _
        (finite_add_right hw0 hw1 H r stage t f (.smul s e) (.smul u f))
        (Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _ (finite_smul_right hw0 hw1 H r stage t s f e)
            (Q'.mul_eqv_congr_left _ _ _ (finite_symm hw0 hw1 H r stage t f e)))
          (finite_smul_right hw0 hw1 H r stage t u f f))
    have hscaledLeft : F (.smul s e) combination ≈ s * (s * F e e + u * F e f) :=
      Q'.eqv_trans _ _ _ (finite_smul_left hw0 hw1 H r stage t s e combination)
        (Q'.mul_eqv_congr_left _ _ _ hleft)
    have hscaledRight : F (.smul u f) combination ≈ u * (s * F e f + u * F f f) :=
      Q'.eqv_trans _ _ _ (finite_smul_left hw0 hw1 H r stage t u f combination)
        (Q'.mul_eqv_congr_left _ _ _ hright)
    have hexpand : F combination combination ≈
        s * (s * F e e + u * F e f) + u * (s * F e f + u * F f f) :=
      Q'.eqv_trans _ _ _
        (finite_add_left hw0 hw1 H r stage t (.smul s e) (.smul u f) combination)
        (Q'.add_eqv_congr' hscaledLeft hscaledRight)
    have hquad : F combination combination ≈
        s*s*F e e + 2*(s*u)*F e f + u*u*F f f :=
      Q'.eqv_trans _ _ _ hexpand (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_add_eqv s (s*F e e) (u*F e f))
          (Q'.mul_add_eqv u (s*F e f) (u*F f f)))
        (YMGap.Continuum.GNSQuotient.GNSData.quad_regroup s u
          (F e e) (F e f) (F f f)))
    have hn : (0 : Q') ≤ F combination combination :=
      chart_square_nonnegative hw0 hw1 H combination ⟨he, hf⟩ r stage t
    exact Q'.le_trans' _ _ _ hn (Q'.le_of_eqv hquad)

/-- Ordinary finite Cauchy--Schwarz for the original full-window selected
action and partition. Both insertions lie within the same centered chart. -/
theorem chartScalar_cauchySchwarz {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (H : Nat) (e f : WindowExpression base)
    (he : Within (2*H) e) (hf : Within (2*H) f) (r stage t : Nat) :
    chartScalar hw0 hw1 H (.mul e f) r stage t *
      chartScalar hw0 hw1 H (.mul e f) r stage t ≤
      chartScalar hw0 hw1 H (.mul e e) r stage t *
        chartScalar hw0 hw1 H (.mul f f) r stage t :=
  (finitePreInnerForm hw0 hw1 base H r stage t).cauchy_schwarz ⟨e, he⟩ ⟨f, hf⟩

end YMGap.Continuum.BF4WilsonSignedTimeFiniteCauchySchwarz

#print axioms YMGap.Continuum.BF4WilsonSignedTimeFiniteCauchySchwarz.chart_square_nonnegative
#print axioms YMGap.Continuum.BF4WilsonSignedTimeFiniteCauchySchwarz.chartScalar_cauchySchwarz
