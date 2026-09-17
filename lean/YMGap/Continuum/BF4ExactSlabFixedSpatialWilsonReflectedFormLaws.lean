/-
# Rational algebra of the actual limiting Wilson reflected form

The form is the existing spatial limit of the literal mixed reflected
product, not a newly supplied positive bilinear form. Coefficient identities
on every original chart and the proved functional laws give rational
bilinearity. The original reflection theorem gives symmetry, and the proved
signed positivity and normalization give its diagonal and unit laws.

The actual Cauchy--Schwarz radical theorem then proves null replacement in
both arguments. These are inputs for the enlarged squared seminorm. No new
carrier, completion, full-observable identification or strict bound is
constructed here; the small-nome and fixed-spacing boundaries are unchanged.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedFormLaws

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonRecenter
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialFunctionalLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedSymmetry
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

attribute [local irreducible] chartScalar spatialLimit

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
  {base : Nat} (hb : 0<base) (H : Nat)

local notation "F" => form hw0 hw1 hsmall hd hs hb H

theorem form_symm (e f : WindowExpression base) (he : Within H e) (hf : Within H f) :
    Equiv (F e f he hf) (F f e hf he) :=
  spatialLimit_reflected_symm hw0 hw1 H e f he hf hsmall hd hs hb

theorem form_nonnegative (e : WindowExpression base) (he : Within H e) :
    leEv (ofQ' 0) (F e e he he) :=
  spatial_reflected_nonnegative hw0 hw1 H e hsmall hd hs hb he

theorem form_one_one : Equiv (F .one .one True.intro True.intro) (ofQ' 1) := by
  refine (spatialLimit_congr hw0 hw1 hsmall hd hs hb H
    (.mul (mirror H .one) .one) .one
    ⟨mirror_within H .one, True.intro⟩ True.intro ?_).trans
      (spatialLimit_one hw0 hw1 hsmall hd hs hb H)
  intro r t
  exact BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics.RatPolyCoeffEqv.one_mul _

theorem form_add_left (e f g : WindowExpression base)
    (he : Within H e) (hf : Within H f) (hg : Within H g) :
    Equiv (F (.add e f) g ⟨he, hf⟩ hg) (add (F e g he hg) (F f g hf hg)) := by
  have heg : Within (2*H) (.mul (mirror H e) g) :=
    ⟨mirror_within H e, within_mono (by omega : H ≤ 2*H) g hg⟩
  have hfg : Within (2*H) (.mul (mirror H f) g) :=
    ⟨mirror_within H f, within_mono (by omega : H ≤ 2*H) g hg⟩
  refine (spatialLimit_congr hw0 hw1 hsmall hd hs hb H
    (.mul (mirror H (.add e f)) g) (.add (.mul (mirror H e) g) (.mul (mirror H f) g))
    ⟨mirror_within H (.add e f), within_mono (by omega : H ≤ 2*H) g hg⟩
    ⟨heg, hfg⟩ ?_).trans (spatialLimit_add hw0 hw1 hsmall hd hs hb H _ _ heg hfg)
  intro r t
  change RatPolyCoeffEqv
    (polyMul (polyAdd (chartInsertion r H t (mirror H e))
      (chartInsertion r H t (mirror H f))) (chartInsertion r H t g)) _
  rw [polyMul_add_left_exact]
  exact RatPolyCoeffEqv.refl _

theorem form_add_right (e f g : WindowExpression base)
    (he : Within H e) (hf : Within H f) (hg : Within H g) :
    Equiv (F e (.add f g) he ⟨hf, hg⟩) (add (F e f he hf) (F e g he hg)) :=
  (form_symm hw0 hw1 hsmall hd hs hb H e (.add f g) he ⟨hf, hg⟩).trans
    ((form_add_left hw0 hw1 hsmall hd hs hb H f g e hf hg he).trans
      (Pivot2.add_congr (form_symm hw0 hw1 hsmall hd hs hb H f e hf he)
        (form_symm hw0 hw1 hsmall hd hs hb H g e hg he)))

theorem form_smul_left (c : Q') (e f : WindowExpression base)
    (he : Within H e) (hf : Within H f) :
    Equiv (F (.smul c e) f he hf) (mul (ofQ' c) (F e f he hf)) := by
  have hef : Within (2*H) (.mul (mirror H e) f) :=
    ⟨mirror_within H e, within_mono (by omega : H ≤ 2*H) f hf⟩
  refine (spatialLimit_congr hw0 hw1 hsmall hd hs hb H
    (.mul (mirror H (.smul c e)) f) (.smul c (.mul (mirror H e) f))
    ⟨mirror_within H (.smul c e), within_mono (by omega : H ≤ 2*H) f hf⟩ hef ?_).trans
      (spatialLimit_smul hw0 hw1 hsmall hd hs hb H c _ hef)
  intro r t
  exact RatPolyCoeffEqv.polyMul_smul_left c _ _

theorem form_smul_right (c : Q') (e f : WindowExpression base)
    (he : Within H e) (hf : Within H f) :
    Equiv (F e (.smul c f) he hf) (mul (ofQ' c) (F e f he hf)) :=
  (form_symm hw0 hw1 hsmall hd hs hb H e (.smul c f) he hf).trans
    ((form_smul_left hw0 hw1 hsmall hd hs hb H c f e hf he).trans
      (Pivot2.mul_congr_right (form_symm hw0 hw1 hsmall hd hs hb H f e hf he)))

private theorem negative_one_mul (A : CReal) : Equiv (mul (ofQ' (-1)) A) (neg A) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 (A.approx n))
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv (A.approx n))))

/-- The signed difference remains literal original Wilson-expression syntax. -/
theorem form_difference_left (e f g : WindowExpression base)
    (he : Within H e) (hf : Within H f) (hg : Within H g) :
    Equiv (F (.add e (.smul (-1) f)) g ⟨he, hf⟩ hg)
      (sub (F e g he hg) (F f g hf hg)) :=
  (form_add_left hw0 hw1 hsmall hd hs hb H e (.smul (-1) f) g he hf hg).trans
    (CReal.add_congr_right
      ((form_smul_left hw0 hw1 hsmall hd hs hb H (-1) f g hf hg).trans
        (negative_one_mul (F f g hf hg))))

theorem form_difference_right (e f g : WindowExpression base)
    (he : Within H e) (hf : Within H f) (hg : Within H g) :
    Equiv (F e (.add f (.smul (-1) g)) he ⟨hf, hg⟩)
      (sub (F e f he hf) (F e g he hg)) :=
  (form_add_right hw0 hw1 hsmall hd hs hb H e f (.smul (-1) g) he hf hg).trans
    (CReal.add_congr_right
      ((form_smul_right hw0 hw1 hsmall hd hs hb H (-1) e g he hg).trans
        (negative_one_mul (F e g he hg))))

theorem form_difference_diagonal (e f : WindowExpression base)
    (he : Within H e) (hf : Within H f) :
    Equiv (F (.add e (.smul (-1) f)) (.add e (.smul (-1) f)) ⟨he, hf⟩ ⟨he, hf⟩)
      (sub (sub (F e e he he) (F e f he hf)) (sub (F f e hf he) (F f f hf hf))) :=
  (form_difference_left hw0 hw1 hsmall hd hs hb H e f (.add e (.smul (-1) f))
    he hf ⟨he, hf⟩).trans
    (Pivot2.add_congr (form_difference_right hw0 hw1 hsmall hd hs hb H e e f he he hf)
      (CReal.neg_congr (form_difference_right hw0 hw1 hsmall hd hs hb H f e f hf he hf)))

/-- A null difference for this actual limiting form permits replacement
against every expression in the same lower window. -/
theorem form_null_left (e e' f : WindowExpression base)
    (he : Within H e) (he' : Within H e') (hf : Within H f)
    (hnull : Equiv
      (F (.add e (.smul (-1) e')) (.add e (.smul (-1) e')) ⟨he, he'⟩ ⟨he, he'⟩)
      (ofQ' 0)) :
    Equiv (F e f he hf) (F e' f he' hf) :=
  Equiv_of_sub_eqv_zero
    ((form_difference_left hw0 hw1 hsmall hd hs hb H e e' f he he' hf).symm.trans
      (spatialLimit_radical_zero hw0 hw1 hsmall hd hs hb H (.add e (.smul (-1) e')) f
        ⟨he, he'⟩ hf hnull))

theorem form_null_congr (e e' f f' : WindowExpression base)
    (he : Within H e) (he' : Within H e') (hf : Within H f) (hf' : Within H f')
    (hleft : Equiv
      (F (.add e (.smul (-1) e')) (.add e (.smul (-1) e')) ⟨he, he'⟩ ⟨he, he'⟩) (ofQ' 0))
    (hright : Equiv
      (F (.add f (.smul (-1) f')) (.add f (.smul (-1) f')) ⟨hf, hf'⟩ ⟨hf, hf'⟩) (ofQ' 0)) :
    Equiv (F e f he hf) (F e' f' he' hf') :=
  (form_null_left hw0 hw1 hsmall hd hs hb H e e' f he he' hf hleft).trans
    ((form_symm hw0 hw1 hsmall hd hs hb H e' f he' hf).trans
      ((form_null_left hw0 hw1 hsmall hd hs hb H f f' e' hf hf' he' hright).trans
        (form_symm hw0 hw1 hsmall hd hs hb H f' e' hf' he')))

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedFormLaws

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedFormLaws.form_symm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedFormLaws.form_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedFormLaws.form_one_one
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedFormLaws.form_add_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedFormLaws.form_add_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedFormLaws.form_smul_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedFormLaws.form_smul_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedFormLaws.form_difference_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedFormLaws.form_difference_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedFormLaws.form_difference_diagonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedFormLaws.form_null_left
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedFormLaws.form_null_congr
