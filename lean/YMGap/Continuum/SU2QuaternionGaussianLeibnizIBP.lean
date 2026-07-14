/-
# Gaussian product integration by parts

This file connects the exact Gaussian expectation to the repository's
existing finite polynomial Leibniz rule.  The result is the bilinear identity

  E[x p q] = E[p' q] + E[p q'].

It is the algebraic input needed for Hermite orthogonality.
-/

import YMGap.Continuum.SU2QuaternionGaussianPolynomialIBP
import YMGap.Continuum.UsumFactorization

namespace YMGap.Continuum.SU2QuaternionGaussianLeibnizIBP

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2QuaternionGaussianPolynomialIBP

local infix:50 " ≈ " => Q'.eqv

set_option maxHeartbeats 500000
set_option maxRecDepth 10000

/-- The already-proved finite formal derivative, named locally to keep its
origin explicit. -/
def formalDerivative (p : Poly) : Poly :=
  YMGap.Continuum.UsumFactorization.pderiv p

private theorem scaleFrom_agrees (s : Nat) : ∀ p : Poly,
    SU2QuaternionGaussianPolynomialIBP.scaleFrom s p =
      YMGap.Continuum.UsumFactorization.scaleFrom s p
  | [] => rfl
  | _ :: cs => by
      simp only [SU2QuaternionGaussianPolynomialIBP.scaleFrom,
        YMGap.Continuum.UsumFactorization.scaleFrom]
      rw [scaleFrom_agrees (s + 1) cs]

theorem pderiv_agrees (p : Poly) :
    SU2QuaternionGaussianPolynomialIBP.pderiv p = formalDerivative p := by
  cases p with
  | nil => rfl
  | cons c cs =>
      unfold SU2QuaternionGaussianPolynomialIBP.pderiv formalDerivative
      unfold YMGap.Continuum.UsumFactorization.pderiv
      exact scaleFrom_agrees 1 cs

/-- The finite Leibniz rule promoted from evaluation equality to the reflected
polynomial setoid. -/
theorem formalDerivative_pmul_polyEqv (p q : Poly) :
    PolyEqv (formalDerivative (pmul p q))
      (padd (pmul (formalDerivative p) q)
        (pmul p (formalDerivative q))) := by
  intro z
  refine Q'.eqv_trans _
    (eval (formalDerivative p) z * eval q z +
      eval p z * eval (formalDerivative q) z) _
    (YMGap.Continuum.UsumFactorization.pderiv_pmul_eval z p q) ?_
  refine Q'.eqv_symm (Q'.eqv_trans _
    (eval (pmul (formalDerivative p) q) z +
      eval (pmul p (formalDerivative q)) z) _
    (eval_padd _ _ z) ?_)
  exact QPoly.q_add_congr
    (eval_pmul (formalDerivative p) q z)
    (eval_pmul p (formalDerivative q) z)

/-- **Gaussian product integration by parts.** -/
theorem gaussianExpectation_mulX_product (p q : Poly) :
    gaussianExpectation (0 :: pmul p q) ≈
      gaussianExpectation (pmul (formalDerivative p) q) +
        gaussianExpectation (pmul p (formalDerivative q)) := by
  have hibp := gaussianExpectation_mulX_eq_deriv (pmul p q)
  rw [pderiv_agrees] at hibp
  refine Q'.eqv_trans _ (gaussianExpectation (formalDerivative (pmul p q))) _
    hibp ?_
  refine Q'.eqv_trans _
    (gaussianExpectation
      (padd (pmul (formalDerivative p) q)
        (pmul p (formalDerivative q)))) _
    (gaussianExpectation_polyEqv (formalDerivative_pmul_polyEqv p q)) ?_
  exact gaussianExpectation_padd _ _

end YMGap.Continuum.SU2QuaternionGaussianLeibnizIBP

#print axioms YMGap.Continuum.SU2QuaternionGaussianLeibnizIBP.pderiv_agrees
#print axioms YMGap.Continuum.SU2QuaternionGaussianLeibnizIBP.formalDerivative_pmul_polyEqv
#print axioms YMGap.Continuum.SU2QuaternionGaussianLeibnizIBP.gaussianExpectation_mulX_product
