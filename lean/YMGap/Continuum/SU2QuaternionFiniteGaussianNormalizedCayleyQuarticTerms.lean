/-
# Weighted four-row terms of the normalized Cayley quartic

This leaf flattens the existing normalized Cayley `F4` polynomial into a
finite signed list of literal ordered four-row words.  The first block comes
from the SAME shared fifteen-term `H4` dot-product list, expanded over its
three-by-three color components.  The second block is the exact
`-4*(sum slot norms)*|a+b+c+d|^2` denominator correction, expanded over its
twelve-by-three row components.

The theorem is coefficientwise polynomial equality.  It does not take an
expectation, estimate a sign, alter the actual plaquette rows, compare the
ORIGINAL law, or establish a physical mass gap.
-/

import YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticExpectation
import YMGap.Continuum.SU2QuaternionFiniteGaussianRowWordWick

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticTerms

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP
open YMGap.Continuum.SU2QuaternionFiniteGaussianDotProductCovariance
open YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyQuarticExpectation
open YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticExpectation
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowWordWick
open YMGap.Continuum.BF4ExactSlabPlaquetteCayleyQuarticDotIdentity

/-- Polynomial represented by a finite weighted term list. -/
def weightedTermPolynomial (terms : List (Q' × RatPoly)) : RatPoly :=
  polySum (terms.map fun term => polySmul term.1 term.2)

private theorem polySum_congr {A : Type} (f g : A → RatPoly) :
    ∀ items : List A,
      (∀ item, item ∈ items → RatPolyCoeffEqv (f item) (g item)) →
      RatPolyCoeffEqv (polySum (items.map f)) (polySum (items.map g))
  | [], _ => RatPolyCoeffEqv.refl _
  | item :: items, h => RatPolyCoeffEqv.add
      (h item List.mem_cons_self)
      (polySum_congr f g items
        (fun other hother => h other (List.mem_cons_of_mem item hother)))

private theorem polySum_map_polySum_flatMap {A : Type}
    (block : A → List RatPoly) : ∀ items : List A,
    RatPolyCoeffEqv
      (polySum (items.map fun item => polySum (block item)))
      (polySum (items.flatMap block))
  | [] => RatPolyCoeffEqv.refl _
  | item :: items =>
      RatPolyCoeffEqv.trans
        (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
          (polySum_map_polySum_flatMap block items))
        (RatPolyCoeffEqv.polySum_append (block item)
          (items.flatMap block))

private theorem polySmul_polySum (weight : Q') : ∀ polynomials : List RatPoly,
    RatPolyCoeffEqv (polySmul weight (polySum polynomials))
      (polySum (polynomials.map fun polynomial =>
        polySmul weight polynomial))
  | [] => RatPolyCoeffEqv.smul_zero weight
  | polynomial :: polynomials =>
      RatPolyCoeffEqv.trans
        (RatPolyCoeffEqv.smul_add weight polynomial (polySum polynomials))
        (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
          (polySmul_polySum weight polynomials))

private theorem weightedTermPolynomial_append
    (left right : List (Q' × RatPoly)) :
    RatPolyCoeffEqv
      (polyAdd (weightedTermPolynomial left) (weightedTermPolynomial right))
      (weightedTermPolynomial (left ++ right)) := by
  unfold weightedTermPolynomial
  simpa only [List.map_append] using
    RatPolyCoeffEqv.polySum_append
      (left.map fun term => polySmul term.1 term.2)
      (right.map fun term => polySmul term.1 term.2)

private theorem weightedTermPolynomial_flatMap {A : Type}
    (block : A → List (Q' × RatPoly)) : ∀ items : List A,
    RatPolyCoeffEqv
      (polySum (items.map fun item => weightedTermPolynomial (block item)))
      (weightedTermPolynomial (items.flatMap block))
  | [] => RatPolyCoeffEqv.refl _
  | item :: items =>
      RatPolyCoeffEqv.trans
        (RatPolyCoeffEqv.add (RatPolyCoeffEqv.refl _)
          (weightedTermPolynomial_flatMap block items))
        (weightedTermPolynomial_append (block item) (items.flatMap block))

/-- Ordered quartic row words obtained by multiplying two finite row dots. -/
def finiteGaussianRowDotQuarticMonomials
    (N leftCount rightCount : Nat)
    (a b c d : Nat → Nat → Q') : List RatPoly :=
  (List.range leftCount).flatMap fun leftComponent =>
    (List.range rightCount).map fun rightComponent =>
      finiteGaussianRowWord N
        [a leftComponent, b leftComponent,
          c rightComponent, d rightComponent]

/-- A product of two literal row dots is exactly the finite sum of its
ordered four-row component words. -/
theorem finiteGaussianRowDot_product_quarticMonomials
    (N leftCount rightCount : Nat)
    (a b c d : Nat → Nat → Q') :
    RatPolyCoeffEqv
      (polyMul (finiteGaussianRowDot N leftCount a b)
        (finiteGaussianRowDot N rightCount c d))
      (polySum (finiteGaussianRowDotQuarticMonomials
        N leftCount rightCount a b c d)) := by
  let leftMonomials := (List.range leftCount).map fun component =>
    finiteGaussianRowWord N [a component, b component]
  let rightMonomials := (List.range rightCount).map fun component =>
    finiteGaussianRowWord N [c component, d component]
  have houter := RatPolyCoeffEqv.polySum_mul_right
    leftMonomials (polySum rightMonomials)
  have hrows : RatPolyCoeffEqv
      (polySum (leftMonomials.map fun leftPolynomial =>
        polyMul leftPolynomial (polySum rightMonomials)))
      (polySum ((List.range leftCount).map fun leftComponent =>
        polySum ((List.range rightCount).map fun rightComponent =>
          finiteGaussianRowWord N
            [a leftComponent, b leftComponent,
              c rightComponent, d rightComponent]))) := by
    unfold leftMonomials rightMonomials
    simp only [List.map_map]
    exact polySum_congr _ _ (List.range leftCount)
      (fun leftComponent _ =>
        RatPolyCoeffEqv.trans
          (RatPolyCoeffEqv.mul_polySum_right
            (finiteGaussianRowWord N
              [a leftComponent, b leftComponent])
            ((List.range rightCount).map fun rightComponent =>
              finiteGaussianRowWord N
                [c rightComponent, d rightComponent]))
          (by
            simp only [List.map_map]
            exact polySum_congr _ _ (List.range rightCount)
              (fun rightComponent _ =>
                finiteGaussianRowWord_append_nonempty N
                  (a leftComponent) (c rightComponent)
                  [b leftComponent] [d rightComponent])))
  have hflat := polySum_map_polySum_flatMap
    (fun leftComponent =>
      (List.range rightCount).map fun rightComponent =>
        finiteGaussianRowWord N
          [a leftComponent, b leftComponent,
            c rightComponent, d rightComponent])
    (List.range leftCount)
  unfold finiteGaussianRowDot finiteGaussianRowDotQuarticMonomials
  exact RatPolyCoeffEqv.trans houter
    (RatPolyCoeffEqv.trans hrows hflat)

/-- Weighted quartic row terms contributed by one signed `H4` dot term. -/
def finiteGaussianH4TermQuarticTerms (N : Nat)
    (slots : Nat → Nat → Nat → Q') (term : H4DotTerm) :
    List (Q' × RatPoly) :=
    (List.range 3).flatMap fun leftComponent =>
      (List.range 3).map fun rightComponent =>
        (Q'.ofInt term.weight,
          finiteGaussianRowWord N
            [slots term.firstLeft leftComponent,
              slots term.firstRight leftComponent,
              slots term.secondLeft rightComponent,
              slots term.secondRight rightComponent])

/-- Weighted quartic row terms of the shared fifteen-term `H4` list. -/
def finiteGaussianCayleyH4QuarticTerms (N : Nat)
    (a b c d : Nat → Nat → Q') : List (Q' × RatPoly) :=
  let slots := gaussianCayleySlot a b c d
  h4DotTerms.flatMap (finiteGaussianH4TermQuarticTerms N slots)

/-- Weighted quartic row terms of the exact denominator correction. -/
def finiteGaussianCayleyDenominatorQuarticTerms (N : Nat)
    (a b c d : Nat → Nat → Q') : List (Q' × RatPoly) :=
  let slots := gaussianCayleySlot a b c d
  let normRows := gaussianCayleyNormRows slots
  let totalRows := gaussianCayleyTotalRows slots
  (List.range 12).flatMap fun normComponent =>
    (List.range 3).map fun totalComponent =>
      (Q'.ofInt (-4),
        finiteGaussianRowWord N
          [normRows normComponent, normRows normComponent,
            totalRows totalComponent, totalRows totalComponent])

/-- Complete weighted quartic term list of the normalized Cayley `F4`. -/
def finiteGaussianNormalizedCayleyH4QuarticTerms (N : Nat)
    (a b c d : Nat → Nat → Q') : List (Q' × RatPoly) :=
  finiteGaussianCayleyH4QuarticTerms N a b c d ++
    finiteGaussianCayleyDenominatorQuarticTerms N a b c d

private theorem finiteGaussianH4TermPolynomial_quarticTerms
    (N : Nat) (slots : Nat → Nat → Nat → Q') (term : H4DotTerm) :
    RatPolyCoeffEqv
      (finiteGaussianH4TermPolynomial N slots term)
      (weightedTermPolynomial
        (finiteGaussianH4TermQuarticTerms N slots term)) := by
  let monomials := finiteGaussianRowDotQuarticMonomials N 3 3
    (slots term.firstLeft) (slots term.firstRight)
    (slots term.secondLeft) (slots term.secondRight)
  have hproduct := finiteGaussianRowDot_product_quarticMonomials N 3 3
    (slots term.firstLeft) (slots term.firstRight)
    (slots term.secondLeft) (slots term.secondRight)
  unfold finiteGaussianH4TermPolynomial finiteGaussianH4TermQuarticTerms
    weightedTermPolynomial
  exact RatPolyCoeffEqv.trans (hproduct.smul (Q'.ofInt term.weight))
    (by
      change RatPolyCoeffEqv
        (polySmul (Q'.ofInt term.weight) (polySum monomials)) _
      exact polySmul_polySum (Q'.ofInt term.weight) monomials)

private theorem finiteGaussianCayleyH4Polynomial_quarticTerms
    (N : Nat) (a b c d : Nat → Nat → Q') :
    RatPolyCoeffEqv (finiteGaussianCayleyH4Polynomial N a b c d)
      (weightedTermPolynomial
        (finiteGaussianCayleyH4QuarticTerms N a b c d)) := by
  let slots := gaussianCayleySlot a b c d
  unfold finiteGaussianCayleyH4Polynomial
    finiteGaussianCayleyH4QuarticTerms
  exact RatPolyCoeffEqv.trans
    (polySum_congr _ _ h4DotTerms
      (fun term _ =>
        finiteGaussianH4TermPolynomial_quarticTerms N slots term))
    (weightedTermPolynomial_flatMap
      (finiteGaussianH4TermQuarticTerms N slots) h4DotTerms)

private theorem finiteGaussianCayleyDenominatorQuarticCorrection_quarticTerms
    (N : Nat) (a b c d : Nat → Nat → Q') :
    RatPolyCoeffEqv
      (finiteGaussianCayleyDenominatorQuarticCorrection N a b c d)
      (weightedTermPolynomial
        (finiteGaussianCayleyDenominatorQuarticTerms N a b c d)) := by
  let slots := gaussianCayleySlot a b c d
  let normRows := gaussianCayleyNormRows slots
  let totalRows := gaussianCayleyTotalRows slots
  let monomials := finiteGaussianRowDotQuarticMonomials N 12 3
    normRows normRows totalRows totalRows
  have hproduct := finiteGaussianRowDot_product_quarticMonomials N 12 3
    normRows normRows totalRows totalRows
  unfold finiteGaussianCayleyDenominatorQuarticCorrection
    finiteGaussianCayleyDenominatorQuarticTerms weightedTermPolynomial
  exact RatPolyCoeffEqv.trans (hproduct.smul (Q'.ofInt (-4)))
    (by
      change RatPolyCoeffEqv
        (polySmul (Q'.ofInt (-4)) (polySum monomials)) _
      exact polySmul_polySum (Q'.ofInt (-4)) monomials)

/-- The literal normalized Cayley `F4` polynomial is exactly the weighted
finite sum of the displayed ordered four-row words. -/
theorem finiteGaussianNormalizedCayleyH4Polynomial_quarticTerms
    (N : Nat) (a b c d : Nat → Nat → Q') :
    RatPolyCoeffEqv
      (finiteGaussianNormalizedCayleyH4Polynomial N a b c d)
      (weightedTermPolynomial
        (finiteGaussianNormalizedCayleyH4QuarticTerms N a b c d)) := by
  unfold finiteGaussianNormalizedCayleyH4Polynomial
    finiteGaussianNormalizedCayleyH4QuarticTerms
  exact RatPolyCoeffEqv.trans
    (RatPolyCoeffEqv.add
      (finiteGaussianCayleyH4Polynomial_quarticTerms N a b c d)
      (finiteGaussianCayleyDenominatorQuarticCorrection_quarticTerms
        N a b c d))
    (weightedTermPolynomial_append
      (finiteGaussianCayleyH4QuarticTerms N a b c d)
      (finiteGaussianCayleyDenominatorQuarticTerms N a b c d))

end YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticTerms

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticTerms.finiteGaussianRowDot_product_quarticMonomials
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticTerms.finiteGaussianNormalizedCayleyH4Polynomial_quarticTerms
