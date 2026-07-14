/-
# Arbitrary univariate Gaussian polynomial-square positivity

The explicit triangular Hermite transform supplies coefficients for every
finite `QPoly`; exact Hermite diagonalization then proves nonnegativity of its
Gaussian square.
-/

import YMGap.Continuum.SU2QuaternionGaussianHermiteTriangular

namespace YMGap.Continuum.SU2QuaternionGaussianPolynomialPositivity

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.SU2QuaternionGaussianPolynomialIBP
open YMGap.Continuum.SU2QuaternionGaussianHermiteOrthogonality
open YMGap.Continuum.SU2QuaternionGaussianHermiteSOS
open YMGap.Continuum.SU2QuaternionGaussianHermiteTriangular

local infix:50 " ≈ " => Q'.eqv

/-- **Every univariate rational polynomial has a nonnegative exact standard
Gaussian square.** -/
theorem gaussianPair_self_nonneg (p : Poly) :
    (0 : Q') ≤ gaussianPair p p := by
  let cs := hermiteExpand p
  let hp := hermiteExpand_synthesis p
  have heq : gaussianPair p p ≈
      gaussianPair (hermiteSynthesisFrom 0 cs)
        (hermiteSynthesisFrom 0 cs) :=
    gaussianPair_polyEqv hp hp
  exact Q'.le_trans' _ _ _ (hermiteSynthesis_square_nonneg 0 cs)
    (Q'.le_of_eqv (Q'.eqv_symm heq))

theorem gaussianExpectation_square_nonneg (p : Poly) :
    (0 : Q') ≤ gaussianExpectation (pmul p p) :=
  gaussianPair_self_nonneg p

end YMGap.Continuum.SU2QuaternionGaussianPolynomialPositivity

#print axioms YMGap.Continuum.SU2QuaternionGaussianPolynomialPositivity.gaussianPair_self_nonneg
#print axioms YMGap.Continuum.SU2QuaternionGaussianPolynomialPositivity.gaussianExpectation_square_nonneg
