/-
# Sharp Cauchy--Schwarz and radical zero for the actual Wilson spatial form

Every finite chart uses one selected original action and one partition.
The signed Wilson expression s*e+r*f remains in the lower window. Its proved
reflected positivity and the exact finite linear laws construct a rational
PreInnerForm, so the existing constructive sharp Cauchy--Schwarz theorem
applies to this actual instance, not to a caller-supplied positive form.

The inequality passes through the unchanged three-regulator diagonal using
the separate convergence data of all three mixed expressions. A zero-norm
expression then pairs to zero by an epsilon-squared argument, without square
roots, division, choice or identifying the different approximation indices.

This is the fixed-spacing, explicit small-nome SU(2) Wilson form. No quotient
completion, observable-coverage identification, strict bound on this enlarged
carrier, spatial symmetry, or physical continuum mass gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialFunctionalLaws
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedSymmetry
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialFunctionalLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedSymmetry
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.OSReconstructionProgress

local infix:50 " ≈ " => Q'.eqv

private def finitePairing {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (H r stage t : Nat) (e f : WindowExpression base) : Q' :=
  chartScalar hw0 hw1 H (.mul (mirror H e) f) r stage t

private theorem finite_add_left {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (H r stage t : Nat) (e f g : WindowExpression base) :
    finitePairing hw0 hw1 H r stage t (.add e f) g ≈
      finitePairing hw0 hw1 H r stage t e g + finitePairing hw0 hw1 H r stage t f g := by
  have hp : RatPolyCoeffEqv
      (chartInsertion r H t (.mul (mirror H (.add e f)) g))
      (chartInsertion r H t (.add (.mul (mirror H e) g) (.mul (mirror H f) g))) := by
    change RatPolyCoeffEqv
      (polyMul (polyAdd (chartInsertion r H t (mirror H e))
        (chartInsertion r H t (mirror H f))) (chartInsertion r H t g)) _
    rw [polyMul_add_left_exact]
    exact RatPolyCoeffEqv.refl _
  exact Q'.eqv_trans _ _ _ (chartScalar_congr hw0 hw1 H _ _ r stage t hp)
    (chartScalar_add hw0 hw1 H _ _ r stage t)

private theorem finite_add_right {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (H r stage t : Nat) (e f g : WindowExpression base) :
    finitePairing hw0 hw1 H r stage t e (.add f g) ≈
      finitePairing hw0 hw1 H r stage t e f + finitePairing hw0 hw1 H r stage t e g := by
  have hp : RatPolyCoeffEqv
      (chartInsertion r H t (.mul (mirror H e) (.add f g)))
      (chartInsertion r H t (.add (.mul (mirror H e) f) (.mul (mirror H e) g))) :=
    RatPolyCoeffEqv.mul_add_right _ _ _
  exact Q'.eqv_trans _ _ _ (chartScalar_congr hw0 hw1 H _ _ r stage t hp)
    (chartScalar_add hw0 hw1 H _ _ r stage t)

private theorem finite_smul_left {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (H r stage t : Nat) (c : Q') (e f : WindowExpression base) :
    finitePairing hw0 hw1 H r stage t (.smul c e) f ≈
      c * finitePairing hw0 hw1 H r stage t e f := by
  have hp : RatPolyCoeffEqv
      (chartInsertion r H t (.mul (mirror H (.smul c e)) f))
      (chartInsertion r H t (.smul c (.mul (mirror H e) f))) :=
    RatPolyCoeffEqv.polyMul_smul_left c _ _
  exact Q'.eqv_trans _ _ _ (chartScalar_congr hw0 hw1 H _ _ r stage t hp)
    (chartScalar_smul hw0 hw1 H c _ r stage t)

private theorem finite_smul_right {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (H r stage t : Nat) (c : Q') (e f : WindowExpression base) :
    finitePairing hw0 hw1 H r stage t e (.smul c f) ≈
      c * finitePairing hw0 hw1 H r stage t e f := by
  have hp : RatPolyCoeffEqv
      (chartInsertion r H t (.mul (mirror H e) (.smul c f)))
      (chartInsertion r H t (.smul c (.mul (mirror H e) f))) :=
    RatPolyCoeffEqv.polyMul_smul_right c _ _
  exact Q'.eqv_trans _ _ _ (chartScalar_congr hw0 hw1 H _ _ r stage t hp)
    (chartScalar_smul hw0 hw1 H c _ r stage t)

private def guardedExpression (base H : Nat) := {e : WindowExpression base // Within H e}

/-- The instance is proved from positivity of the actual signed Wilson combination. -/
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
    have he : Within H e := x.property
    have hf : Within H f := y.property
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
            (Q'.mul_eqv_congr_left _ _ _
              (chartScalar_reflected_symm hw0 hw1 H f e hf he r stage t)))
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
    have hquad : F combination combination ≈ s*s*F e e + 2*(s*u)*F e f + u*u*F f f :=
      Q'.eqv_trans _ _ _ hexpand (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_add_eqv s (s*F e e) (u*F e f))
          (Q'.mul_add_eqv u (s*F e f) (u*F f f)))
        (YMGap.Continuum.GNSQuotient.GNSData.quad_regroup s u (F e e) (F e f) (F f f)))
    have hn : (0 : Q') ≤ F combination combination :=
      chartScalar_reflected_nonnegative hw0 hw1 H combination ⟨he, hf⟩ r stage t
    exact Q'.le_trans' _ _ _ hn (Q'.le_of_eqv hquad)

/-- Sharp finite CS for the original chart scalar with its SAME reciprocal partition. -/
theorem chartScalar_cauchySchwarz {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base : Nat} (H : Nat) (e f : WindowExpression base) (he : Within H e) (hf : Within H f)
    (r stage t : Nat) :
    chartScalar hw0 hw1 H (.mul (mirror H e) f) r stage t *
      chartScalar hw0 hw1 H (.mul (mirror H e) f) r stage t ≤
      chartScalar hw0 hw1 H (.mul (mirror H e) e) r stage t *
        chartScalar hw0 hw1 H (.mul (mirror H f) f) r stage t :=
  (finitePreInnerForm hw0 hw1 base H r stage t).cauchy_schwarz ⟨e, he⟩ ⟨f, hf⟩

/-- The already constructed spatial limit of the actual mixed reflected product. -/
def form {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {base : Nat} (hb : 0<base) (H : Nat) (e f : WindowExpression base)
    (he : Within H e) (hf : Within H f) : CReal :=
  spatialLimit hw0 hw1 H (.mul (mirror H e) f)
    ⟨within_mapOffsets (fun offset => 2*H-offset) (fun offset _ => Nat.sub_le (2*H) offset) e he,
      within_mono (by omega : H ≤ 2*H) f hf⟩ hsmall hd hs hb

attribute [local irreducible] chartScalar spatialLimit

/-- All three scalar limits retain their OWN original convergence witnesses. -/
theorem spatialLimit_cauchySchwarz {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {base : Nat} (hb : 0<base) (H : Nat) (e f : WindowExpression base)
    (he : Within H e) (hf : Within H f) :
    leEv (mul (form hw0 hw1 hsmall hd hs hb H e f he hf)
        (form hw0 hw1 hsmall hd hs hb H e f he hf))
      (mul (form hw0 hw1 hsmall hd hs hb H e e he he)
        (form hw0 hw1 hsmall hd hs hb H f f hf hf)) := by
  have hxy := spatial_diagonal_converges hw0 hw1 H (.mul (mirror H e) f)
    ⟨mirror_within H e, within_mono (by omega : H ≤ 2*H) f hf⟩ hsmall hd hs hb
  have hxx := spatial_diagonal_converges hw0 hw1 H (.mul (mirror H e) e)
    ⟨mirror_within H e, within_mono (by omega : H ≤ 2*H) e he⟩ hsmall hd hs hb
  have hyy := spatial_diagonal_converges hw0 hw1 H (.mul (mirror H f) f)
    ⟨mirror_within H f, within_mono (by omega : H ≤ 2*H) f hf⟩ hsmall hd hs hb
  refine leEv_of_convergesTo_le
    (YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general hxy hxy)
    (YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general hxx hyy) ?_
  intro n epsilon hepsilon
  refine ⟨0, fun i _ => ?_⟩
  change chartScalar hw0 hw1 H (.mul (mirror H e) f) n n n *
      chartScalar hw0 hw1 H (.mul (mirror H e) f) n n n ≤
    chartScalar hw0 hw1 H (.mul (mirror H e) e) n n n *
      chartScalar hw0 hw1 H (.mul (mirror H f) f) n n n + epsilon
  exact Q'.le_trans' _ _ _ (chartScalar_cauchySchwarz hw0 hw1 H e f he hf n n n)
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

/-- The radical of this SAME limiting mixed form pairs to zero. -/
theorem spatialLimit_radical_zero {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
    {base : Nat} (hb : 0<base) (H : Nat) (e f : WindowExpression base)
    (he : Within H e) (hf : Within H f)
    (hnull : Equiv (form hw0 hw1 hsmall hd hs hb H e e he he) (ofQ' 0)) :
    Equiv (form hw0 hw1 hsmall hd hs hb H e f he hf) (ofQ' 0) :=
  zero_of_square_le_zero _ (leEv_trans
    (spatialLimit_cauchySchwarz hw0 hw1 hsmall hd hs hb H e f he hf)
    (leEv_of_equiv ((YMGap.Continuum.Pivot2.mul_congr_left hnull).trans
      (SumOfSquares.Equiv_of_approx_eqv (fun n =>
        Q'.zero_mul_eqv ((form hw0 hw1 hsmall hd hs hb H f f hf hf).approx n))))))

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz.chartScalar_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz.form
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz.spatialLimit_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz.spatialLimit_radical_zero
