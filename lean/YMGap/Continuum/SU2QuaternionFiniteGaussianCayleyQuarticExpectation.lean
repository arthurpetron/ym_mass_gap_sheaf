/-
# Finite Gaussian expectation of the exact Cayley quartic

The exact rational Cayley H4 was rewritten in
`BF4ExactSlabPlaquetteCayleyQuarticDotIdentity` as one fixed list of fifteen
signed products of three-component dot products.  This leaf lifts that SAME
term list to arbitrary finite rational Gaussian row triples and computes its
expectation entirely in finite Gram data.  Each quartic term uses the checked
raw dot-product fourth moment, so both its disconnected Gram-trace product and
its two connected cross-pairings are retained.

This is an expectation-level reference identity.  It is not an original-law
comparison, a sign estimate, a denominator-relative remainder bound, a
uniform-in-cutoff statement, or a physical mass gap.  Variables outside the
finite Gaussian prefix are evaluated at ONE by the existing evaluator.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteCayleyQuarticDotIdentity
import YMGap.Continuum.SU2QuaternionFiniteGaussianDotProductCovariance

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyQuarticExpectation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP
open YMGap.Continuum.SU2QuaternionFiniteGaussianDoubleStein
open YMGap.Continuum.SU2QuaternionFiniteGaussianRowGram
open YMGap.Continuum.SU2QuaternionFiniteGaussianDotProductCovariance
open YMGap.Continuum.BF4ExactSlabPlaquetteCayleyQuarticDotIdentity

local infix:50 " ≈ " => Q'.eqv

/-- Four directed Gaussian row triples in the Cayley slot order.  Components
outside `0,1,2` and slots outside `0,1,2` are never read by the exact term
list. -/
def gaussianCayleySlot
    (a b c d : Nat → Nat → Q') : Nat → Nat → Nat → Q'
  | 0 => a
  | 1 => b
  | 2 => c
  | _ => d

def finiteGaussianH4TermPolynomial (N : Nat)
    (slots : Nat → Nat → Nat → Q') (term : H4DotTerm) : RatPoly :=
  polySmul (Q'.ofInt term.weight)
    (polyMul
      (finiteGaussianRowDot N 3
        (slots term.firstLeft) (slots term.firstRight))
      (finiteGaussianRowDot N 3
        (slots term.secondLeft) (slots term.secondRight)))

/-- Literal finite-Gaussian polynomial lift of the exact fifteen-term H4. -/
def finiteGaussianCayleyH4Polynomial (N : Nat)
    (a b c d : Nat → Nat → Q') : RatPoly :=
  polySum (h4DotTerms.map
    (finiteGaussianH4TermPolynomial N (gaussianCayleySlot a b c d)))

def finiteGaussianH4TermGram (N : Nat)
    (slots : Nat → Nat → Nat → Q') (term : H4DotTerm) : Q' :=
  Q'.ofInt term.weight *
    (finiteRowDotGram N 3
          (slots term.firstLeft) (slots term.firstRight) *
        finiteRowDotGram N 3
          (slots term.secondLeft) (slots term.secondRight) +
      finiteRowDotConnectedGram N 3 3
        (slots term.firstLeft) (slots term.firstRight)
        (slots term.secondLeft) (slots term.secondRight))

/-- Explicit finite Gram value of the exact H4 expectation. -/
def finiteGaussianCayleyH4GramExpectation (N : Nat)
    (a b c d : Nat → Nat → Q') : Q' :=
  qListSum (h4DotTerms.map
    (finiteGaussianH4TermGram N (gaussianCayleySlot a b c d)))

private theorem gaussian_zero (N : Nat) :
    finiteProductGaussian N polyZero ≈ 0 := by
  rw [finiteProductGaussian_probe]
  exact Q'.eqv_refl _

private theorem gaussian_add (N : Nat) (p q : RatPoly) :
    finiteProductGaussian N (polyAdd p q) ≈
      finiteProductGaussian N p + finiteProductGaussian N q := by
  rw [finiteProductGaussian_probe, finiteProductGaussian_probe, finiteProductGaussian_probe]
  exact ratWeightedSum_add (finiteGaussianMono N) p q

private theorem gaussian_smul (N : Nat) (weight : Q') (p : RatPoly) :
    finiteProductGaussian N (polySmul weight p) ≈
      weight * finiteProductGaussian N p := by
  rw [finiteProductGaussian_probe, finiteProductGaussian_probe]
  exact ratWeightedSum_smul (finiteGaussianMono N) weight p

private theorem gaussian_polySum (N : Nat) : ∀ polynomials : List RatPoly,
    finiteProductGaussian N (polySum polynomials) ≈
      qListSum (polynomials.map fun polynomial =>
        finiteProductGaussian N polynomial)
  | [] => gaussian_zero N
  | polynomial :: polynomials =>
      Q'.eqv_trans _ _ _ (gaussian_add N polynomial (polySum polynomials))
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (gaussian_polySum N polynomials))

private theorem qListSum_congr {A : Type} (f g : A → Q') : ∀ ids : List A,
    (∀ item, item ∈ ids → f item ≈ g item) →
    qListSum (ids.map f) ≈ qListSum (ids.map g)
  | [], _ => Q'.eqv_refl _
  | item :: items, h => Q'.add_eqv_congr' (h item List.mem_cons_self)
      (qListSum_congr f g items
        (fun other hother => h other (List.mem_cons_of_mem item hother)))

private theorem finiteProductGaussian_H4Term (N : Nat)
    (slots : Nat → Nat → Nat → Q') (term : H4DotTerm) :
    finiteProductGaussian N
        (finiteGaussianH4TermPolynomial N slots term) ≈
      finiteGaussianH4TermGram N slots term := by
  exact Q'.eqv_trans _ _ _
    (gaussian_smul N (Q'.ofInt term.weight)
      (polyMul
        (finiteGaussianRowDot N 3
          (slots term.firstLeft) (slots term.firstRight))
        (finiteGaussianRowDot N 3
          (slots term.secondLeft) (slots term.secondRight))))
    (Q'.mul_eqv_congr_left _ _ _
      (finiteProductGaussian_row_dot_product N 3 3
        (slots term.firstLeft) (slots term.firstRight)
        (slots term.secondLeft) (slots term.secondRight)))

/-- The finite product-Gaussian expectation of the literal exact-H4 lift is
the displayed finite sum of Gram-trace and connected cross-pairing values. -/
theorem finiteProductGaussian_cayleyH4
    (N : Nat) (a b c d : Nat → Nat → Q') :
    finiteProductGaussian N
        (finiteGaussianCayleyH4Polynomial N a b c d) ≈
      finiteGaussianCayleyH4GramExpectation N a b c d := by
  unfold finiteGaussianCayleyH4Polynomial
    finiteGaussianCayleyH4GramExpectation
  exact Q'.eqv_trans _ _ _
    (gaussian_polySum N
      (h4DotTerms.map
        (finiteGaussianH4TermPolynomial N
          (gaussianCayleySlot a b c d))))
    (by
      simp only [List.map_map]
      exact qListSum_congr _ _ h4DotTerms
        (fun term _ =>
          finiteProductGaussian_H4Term N
            (gaussianCayleySlot a b c d) term))

end YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyQuarticExpectation

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyQuarticExpectation.finiteProductGaussian_cayleyH4
