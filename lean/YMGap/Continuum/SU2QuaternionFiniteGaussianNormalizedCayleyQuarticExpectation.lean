/-
# Finite Gaussian expectation of the denominator-normalized Cayley quartic

The exact division-free Cayley identity identifies the normalized quartic
coefficient as

  F4 = H4 - (sum of four slot norms) * H2,
  H2 = 4 * norm(sum of the four directed slots).

This leaf computes the finite product-Gaussian expectation of the literal
row-polynomial lift of F4.  The H4 term is the checked fifteen-term Cayley
quartic.  The denominator correction is represented as a product of a
twelve-component slot/color norm sum and the three-component norm of the
directed slot sum, so the existing arbitrary-component dot-product fourth
moment computes it without any division.

This remains finite reference algebra.  It gives no sign, uniform remainder,
original-law comparison, radial-ratio transfer or physical mass gap.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteCayleyNormalizedQuartic
import YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyQuarticExpectation

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticExpectation

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
open YMGap.Continuum.SU2QuaternionFiniteGaussianCayleyQuarticExpectation

local infix:50 " ≈ " => Q'.eqv

/-- Twelve separate slot/color rows whose squared dot is the sum of the four
directed slot norms.  Only indices below twelve are consumed. -/
def gaussianCayleyNormRows
    (slots : Nat → Nat → Nat → Q') : Nat → Nat → Q'
  | 0 => slots 0 0
  | 1 => slots 0 1
  | 2 => slots 0 2
  | 3 => slots 1 0
  | 4 => slots 1 1
  | 5 => slots 1 2
  | 6 => slots 2 0
  | 7 => slots 2 1
  | 8 => slots 2 2
  | 9 => slots 3 0
  | 10 => slots 3 1
  | _ => slots 3 2

/-- Three color rows of the directed sum `a+b+c+d`. -/
def gaussianCayleyTotalRows
    (slots : Nat → Nat → Nat → Q') (component coordinate : Nat) : Q' :=
  ((slots 0 component coordinate + slots 1 component coordinate) +
    slots 2 component coordinate) + slots 3 component coordinate

/-- Polynomial lift of `-(sum norms)*H2`, with the exact factor `H2=4|sum|²`. -/
def finiteGaussianCayleyDenominatorQuarticCorrection (N : Nat)
    (a b c d : Nat → Nat → Q') : RatPoly :=
  let slots := gaussianCayleySlot a b c d
  polySmul (Q'.ofInt (-4))
    (polyMul
      (finiteGaussianRowDot N 12
        (gaussianCayleyNormRows slots) (gaussianCayleyNormRows slots))
      (finiteGaussianRowDot N 3
        (gaussianCayleyTotalRows slots) (gaussianCayleyTotalRows slots)))

/-- Literal finite-Gaussian polynomial lift of the exact normalized F4. -/
def finiteGaussianNormalizedCayleyH4Polynomial (N : Nat)
    (a b c d : Nat → Nat → Q') : RatPoly :=
  polyAdd (finiteGaussianCayleyH4Polynomial N a b c d)
    (finiteGaussianCayleyDenominatorQuarticCorrection N a b c d)

def finiteGaussianCayleyDenominatorQuarticCorrectionGram (N : Nat)
    (a b c d : Nat → Nat → Q') : Q' :=
  let slots := gaussianCayleySlot a b c d
  Q'.ofInt (-4) *
    (finiteRowDotGram N 12
          (gaussianCayleyNormRows slots) (gaussianCayleyNormRows slots) *
        finiteRowDotGram N 3
          (gaussianCayleyTotalRows slots) (gaussianCayleyTotalRows slots) +
      finiteRowDotConnectedGram N 12 3
        (gaussianCayleyNormRows slots) (gaussianCayleyNormRows slots)
        (gaussianCayleyTotalRows slots) (gaussianCayleyTotalRows slots))

/-- Exact finite Gram value of the normalized quartic expectation. -/
def finiteGaussianNormalizedCayleyH4GramExpectation (N : Nat)
    (a b c d : Nat → Nat → Q') : Q' :=
  finiteGaussianCayleyH4GramExpectation N a b c d +
    finiteGaussianCayleyDenominatorQuarticCorrectionGram N a b c d

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

private theorem finiteProductGaussian_denominator_quartic_correction
    (N : Nat) (a b c d : Nat → Nat → Q') :
    finiteProductGaussian N
        (finiteGaussianCayleyDenominatorQuarticCorrection N a b c d) ≈
      finiteGaussianCayleyDenominatorQuarticCorrectionGram N a b c d := by
  let slots := gaussianCayleySlot a b c d
  exact Q'.eqv_trans _ _ _
    (gaussian_smul N (Q'.ofInt (-4))
      (polyMul
        (finiteGaussianRowDot N 12
          (gaussianCayleyNormRows slots) (gaussianCayleyNormRows slots))
        (finiteGaussianRowDot N 3
          (gaussianCayleyTotalRows slots) (gaussianCayleyTotalRows slots))))
    (Q'.mul_eqv_congr_left _ _ _
      (finiteProductGaussian_row_dot_product N 12 3
        (gaussianCayleyNormRows slots) (gaussianCayleyNormRows slots)
        (gaussianCayleyTotalRows slots) (gaussianCayleyTotalRows slots)))

/-- Exact finite product-Gaussian expectation of the denominator-normalized
Cayley quartic coefficient F4. -/
theorem finiteProductGaussian_normalized_cayleyH4
    (N : Nat) (a b c d : Nat → Nat → Q') :
    finiteProductGaussian N
        (finiteGaussianNormalizedCayleyH4Polynomial N a b c d) ≈
      finiteGaussianNormalizedCayleyH4GramExpectation N a b c d := by
  exact Q'.eqv_trans _ _ _
    (gaussian_add N
      (finiteGaussianCayleyH4Polynomial N a b c d)
      (finiteGaussianCayleyDenominatorQuarticCorrection N a b c d))
    (Q'.add_eqv_congr'
      (finiteProductGaussian_cayleyH4 N a b c d)
      (finiteProductGaussian_denominator_quartic_correction N a b c d))

end YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticExpectation

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianNormalizedCayleyQuarticExpectation.finiteProductGaussian_normalized_cayleyH4
